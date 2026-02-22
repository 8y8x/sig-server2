'use strict';

const fs = require('node:fs');
const readline = require('node:readline');
const uws = require('uWebSockets.js');

const settings = require('./settings.json');

const textDecoder = new TextDecoder();
const textEncoder = new TextEncoder();
const EMPTY_BUFFER_U8 = new Uint8Array(0);
const EMPTY_BUFFER_DAT = new DataView(EMPTY_BUFFER_U8.buffer);
const EMPTY_STRING_U8 = new Uint8Array([0]);
const EMPTY_STRING_DAT = new DataView(EMPTY_STRING_U8.buffer);
const writerU8 = new Uint8Array(2 ** 22); // 4MB is more than enough, even for the most extreme cases
const writerDat = new DataView(writerU8.buffer);

const encodeUtf8AsU8 = s => {
	const base = textEncoder.encode(s);
	const u8 = new Uint8Array(base.length + 1); // null-terminated
	for (let o = 0; o < base.length; ++o) u8[o] = base[o] || 0xff; // get rid of null terminators
	return u8;
};

//========== bitgrid ===================================================================================================

// undefined behaviour occurs if a cell ever exists beyond the bitgrid, just keep it in mind
// (the width and height) get all messed up
const BITGRID_TILE_SIZE = Math.max(2500, (settings.worldMapW * 2 + 3000) / 32);
const bitgridTiles = [];
for (let i = 0; i < 1024; ++i) bitgridTiles.push(new Set());

const bitgridAdd = cell => {
	const xmin = ((cell.x + settings.worldMapW - cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	const xmax = ((cell.x + settings.worldMapW + cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	const ymin = ((cell.y + settings.worldMapH - cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	const ymax = ((cell.y + settings.worldMapH + cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	cell.bgXmin = xmin; cell.bgXmax = xmax; cell.bgYmin = ymin; cell.bgYmax = ymax;

	for (let x = xmin; x <= xmax; ++x) {
		for (let y = ymin; y <= ymax; ++y) {
			bitgridTiles[y * 32 + x].add(cell);
		}
	}
};

const bitgridUpdate = cell => {
	const { bgXmin, bgXmax, bgYmin, bgYmax } = cell;
	const xmin = ((cell.x + settings.worldMapW - cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	const xmax = ((cell.x + settings.worldMapW + cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	const ymin = ((cell.y + settings.worldMapH - cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	const ymax = ((cell.y + settings.worldMapH + cell.r) / BITGRID_TILE_SIZE) & 0x1f;
	
	if (xmin === bgXmin && xmax === bgXmax && ymin === bgYmin && ymax === bgYmax) return; // shortcut
	cell.bgXmin = xmin; cell.bgXmax = xmax; cell.bgYmin = ymin; cell.bgYmax = ymax;

	const minXmin = bgXmin < xmin ? bgXmin : xmin;
	const maxXmax = bgXmax > xmax ? bgXmax : xmax;
	const minYmin = bgYmin < ymin ? bgYmin : ymin;
	const maxYmax = bgYmax > ymax ? bgYmax : ymax;

	for (let x = minXmin; x <= maxXmax; ++x) {
		const xInOld = bgXmin <= x && x <= bgXmax;
		const xInNew = xmin <= x && x <= xmax;
		for (let y = minYmin; y <= maxYmax; ++y) {
			const inOld = xInOld && bgYmin <= y && y <= bgYmax;
			const inNew = xInNew && ymin <= y && y <= ymax;
			if (inNew && !inOld) bitgridTiles[y * 32 + x].add(cell);
			else if (!inNew && inOld) bitgridTiles[y * 32 + x].delete(cell);
		}
	}
};

const bitgridRemove = cell => {
	const { bgXmin, bgXmax, bgYmin, bgYmax } = cell;
	for (let x = bgXmin; x <= bgXmax; ++x) {
		for (let y = bgYmin; y <= bgYmax; ++y) {
			bitgridTiles[y * 32 + x].delete(cell);
		}
	}
};

const bitgridSearch = (xmin, xmax, ymin, ymax, cb) => {
	for (let x = xmin; x <= xmax; ++x) {
		for (let y = ymin; y <= ymax; ++y) {
			for (const cell of bitgridTiles[y * 32 + x]) {
				// no duplicates
				if ((xmin <= cell.bgXmin && cell.bgXmin < x) || (ymin <= cell.bgYmin && cell.bgYmin < y)) continue;
				if (cb(cell)) return true;
			}
		}
	}

	return false;
};

//========== world =====================================================================================================

const [CELL_TYPE_PLAYER, CELL_TYPE_PELLET, CELL_TYPE_EJECT, CELL_TYPE_VIRUS] = [Symbol(), Symbol(), Symbol(), Symbol()];
const [PLAYER_STATE_IDLE, PLAYER_STATE_PLAYING, PLAYER_STATE_ROAM, PLAYER_STATE_SPECTATE, PLAYER_STATE_LIMBO]
	= [Symbol(), Symbol(), Symbol(), Symbol(), Symbol()];
const PLAYER_OWNER_SERVER = {
	bot: false,
	camera: { x: 0, y: 0, scale: 1 },
	clanU8: EMPTY_STRING_U8,
	disconnectedAt: 0,
	lastW: 0,
	minionCommander: undefined,
	mouseX: 0,
	mouseY: 0,
	nameU8: EMPTY_STRING_U8,
	owned: new Set(),
	rgb: 0x7f7f7f,
	q: false,
	showClanmates: false,
	skinU8: EMPTY_STRING_U8,
	spawn: undefined,
	splits: 0,
	state: PLAYER_STATE_IDLE,
	sub: false,
	updated: -Infinity,
	visibleCells: new Set(),
	w: false,
	ws: {},
}
const PLAYER_BOT_NAMES_U8 = settings.worldPlayerBotNames.map(x => encodeUtf8AsU8(x.replace('{*}', '')));
const PLAYER_BOT_SKINS_U8 = settings.worldPlayerBotSkins.map(encodeUtf8AsU8);

const MINION_SPAWN = { nameU8: encodeUtf8AsU8(settings.minionName), skinU8: EMPTY_STRING_U8, spectating: false, sub: false };

const SQRT2 = Math.sqrt(2);
const WORLD_EAT_MULT = Math.sqrt(1.3); // must be 30% bigger in mass to eat a cell
const WORLD_EAT_OVERLAP_MULT = 1 / 3;

const metricsPointsLabels = [];
const metricsMeasurements = [];

const boostingCells = [];
const playerCells = [];
const players = new Set();
const playerBotAi = new WeakMap();
let connections = 0;
let nextCellId = 1;
let now = 0; // current tick
let pellets = 0;
let viruses = 0;

let statsU8 = new Uint8Array([0xfe, 0x7b, 0x7d, 0]); // \xfe{}\0

const randomColors = new Uint32Array(1536);
for (let shade = 0; shade < 256; ++shade) {
	randomColors.set([
		0x10ff00 | shade, 0xff1000 | shade, // random red component
		0x1000ff | (shade << 8), 0xff0010 | (shade << 8), // random green component
		0x0010ff | (shade << 16), 0x00ff10 | (shade << 16), // random blue component
	], shade * 6);
}

const bounce = (cell, fromBoost) => {
	const r = cell.r / 2;
	if (cell.x - r < -settings.worldMapW) {
		cell.x = -settings.worldMapW + r;
		if (fromBoost) cell.boostUnitX *= -1;
	} else if (settings.worldMapW < cell.x + r) {
		cell.x = settings.worldMapW - r;
		if (fromBoost) cell.boostUnitX *= -1;
	}
	if (cell.y - r < -settings.worldMapW) {
		cell.y = -settings.worldMapW + r;
		if (fromBoost) cell.boostUnitY *= -1;
	} else if (settings.worldMapW < cell.y + r) {
		cell.y = settings.worldMapW - r;
		if (fromBoost) cell.boostUnitY *= -1;
	}
};

const add = cellSkeleton => {
	const cell = {
		type: CELL_TYPE_EJECT,
		id: nextCellId++,
		x: 0, y: 0, r: 100,
		rgb: 0x7f7f7f,
		born: now, moved: now, dead: false, deadTo: 0,
		owner: PLAYER_OWNER_SERVER,
		boostUnitX: 0, boostUnitY: 0, boostMagnitude: 0,
		moveU8: EMPTY_BUFFER_U8, moveDat: EMPTY_BUFFER_DAT,
		firstU8: EMPTY_BUFFER_U8, firstDat: EMPTY_BUFFER_DAT,
		mergeable: false, fed: 0,
		...cellSkeleton,
	};
	encode(cell);
	bitgridAdd(cell);
	return cell;
};

const remove = cell => {
	bitgridRemove(cell);
	if (cell.type === CELL_TYPE_PLAYER) cell.owner.owned.delete(cell);
	else if (cell.type === CELL_TYPE_PELLET) --pellets;
	else if (cell.type === CELL_TYPE_VIRUS) --viruses;
	// the cell will be removed from boostingCells and playerCells later
};

const leftEatsRight = (leftCell, rightCell) => {
	if (leftCell.type === CELL_TYPE_PLAYER) {
		// players eat everything, but minions only eat minions
		if (leftCell.owner.minionCommander && !rightCell.owner.minionCommander) return false;
		if (leftCell.owner === rightCell.owner) return leftCell.mergeable && rightCell.mergeable
			&& Math.hypot(leftCell.x - rightCell.x, leftCell.y - rightCell.y) <= leftCell.r - rightCell.r * WORLD_EAT_OVERLAP_MULT;
	} else if (leftCell.type === CELL_TYPE_PELLET) {
		// pellets don't eat anything
		return false;
	} else if (leftCell.type === CELL_TYPE_VIRUS) {
		// viruses eat ejects but nothing else
		if (rightCell.type !== CELL_TYPE_EJECT) return false;
	} else if (leftCell.type === CELL_TYPE_EJECT) {
		// ejects don't eat anything
		return false;
	}

	return leftCell.r > rightCell.r * WORLD_EAT_MULT
		&& Math.hypot(leftCell.x - rightCell.x, leftCell.y - rightCell.y) <= leftCell.r - rightCell.r * WORLD_EAT_OVERLAP_MULT;
};
const leftCollidesRight = (leftCell, rightCell) => {
	if (leftCell.type === CELL_TYPE_EJECT && rightCell.type === CELL_TYPE_EJECT) return true;

	if (leftCell.type !== CELL_TYPE_PLAYER || rightCell.type !== CELL_TYPE_PLAYER) return false;
	if (leftCell.owner !== rightCell.owner) return false;
	const leftLifetime = now - leftCell.born;
	const rightLifetime = now - rightCell.born;
	// .mergeable is only written here. it will always become true the moment it can be
	leftCell.mergeable ||=
		leftLifetime >= 25 * (settings.playerMergeTime + leftCell.r * settings.playerMergeTimeIncrease);
	rightCell.mergeable ||=
		rightLifetime >= 25 * (settings.playerMergeTime + rightCell.r * settings.playerMergeTimeIncrease);
	return (!leftCell.mergeable || !rightCell.mergeable)
		&& leftLifetime >= settings.playerNoCollideDelay
		&& rightLifetime >= settings.playerNoCollideDelay;
};

const safeSpawnPos = (radius) => {
	for (let i = 0; i < settings.worldSafeSpawnTries; ++i) {
		const x = (Math.random() * 2 - 1) * (settings.worldMapW - radius);
		const y = (Math.random() * 2 - 1) * (settings.worldMapH - radius);

		const xmin = ((x + settings.worldMapW - radius) / BITGRID_TILE_SIZE) & 0x1f;
		const xmax = ((x + settings.worldMapW + radius) / BITGRID_TILE_SIZE) & 0x1f;
		const ymin = ((y + settings.worldMapH - radius) / BITGRID_TILE_SIZE) & 0x1f;
		const ymax = ((y + settings.worldMapH + radius) / BITGRID_TILE_SIZE) & 0x1f;
		if (!bitgridSearch(xmin, xmax, ymin, ymax, cell => {
			if (cell.type === CELL_TYPE_PELLET) return;
			if (x - radius <= cell.x + cell.r && cell.x - cell.r <= x + radius
				&& y - radius <= cell.y + cell.r && cell.y - cell.r <= y + radius)
				return true;
		})) {
			return [x, y];
		}
	}

	const x = (Math.random() * 2 - 1) * (settings.worldMapW - radius);
	const y = (Math.random() * 2 - 1) * (settings.worldMapH - radius);
	return [x, y];
};

const encode = cell => {
	let { moveU8, moveDat } = cell;
	const moveByteLength = 14 + cell.owner.clanU8.length;
	if (moveU8.length !== moveByteLength) {
		cell.moveU8 = moveU8 = new Uint8Array(moveByteLength);
		cell.moveDat = moveDat = new DataView(moveU8.buffer);
	}

	moveDat.setUint32(0, cell.id, true);
	moveDat.setInt16(4, cell.x, true);
	moveDat.setInt16(6, cell.y, true);
	moveDat.setUint16(8, cell.r, true);

	let flags = 0;
	if (cell.type === CELL_TYPE_VIRUS) flags |= 1;
	if (cell.type === CELL_TYPE_EJECT) flags |= 0x20;
	moveU8[10] = flags;
	// moveU8[11] = 0; // sigmally: isUpdate, this is never used
	// moveU8[12] = 0; // sigmally: isPlayer, this is never used
	moveU8[13] = cell.owner.sub ? 1 : 0; // sigmally

	moveU8.set(cell.owner.clanU8, 14); // sigmally

	let { firstDat, firstU8 } = cell;
	const firstByteLength = moveByteLength + 3 + cell.owner.skinU8.length + cell.owner.nameU8.length;
	if (firstDat.byteLength !== firstByteLength) {
		cell.firstU8 = firstU8 = new Uint8Array(firstByteLength);
		cell.firstDat = firstDat = new DataView(firstU8.buffer);
		cell.firstU8.set(moveU8);
		cell.firstU8[10] |= 2 | 4 | 8; // add more flags (color, skin, name)

		let o = moveU8.length;
		(firstDat.setUint32(o, cell.rgb, true), o += 3);
		(firstU8.set(cell.owner.skinU8, o), o += cell.owner.skinU8.length);
		firstU8.set(cell.owner.nameU8, o);
	} else {
		firstDat.setInt16(4, cell.x, true);
		firstDat.setInt16(6, cell.y, true);
		firstDat.setUint16(8, cell.r, true);
	}
};

let lastLargestPlayerVisibleCells = new Set();
const worldEatArray = [];
const worldRigidArray = [];
const worldPacketEatArray = [];
const worldPacketAddArray = [];
const worldPacketUpdArray = [];
const worldPacketDelArray = [];
const worldTick = () => {
	const start = performance.now();

	// #1 update world
	const framePoints = [];
	let lastPoint = start;
	const tickMeasurement = label => {
		metricsPointsLabels[framePoints.length] = label;
		const now = performance.now();
		framePoints.push(now - lastPoint);
		lastPoint = now;
	};

	if (nextCellId >= 4e9) nextCellId = 1;

	for (; pellets < settings.pelletCount; ++pellets) {
		const [x, y] = safeSpawnPos(settings.pelletMinSize); // TODO, this should probably not be safeSpawnPos
		add({ type: CELL_TYPE_PELLET, x, y, r: settings.pelletMinSize, rgb: randomColors[~~(Math.random() * 1536)] });
	}

	if (pellets > settings.pelletCount) {
		// only happens very rarely
		const fraction = pellets / settings.pelletCount;
		let i = 0;
		const removalQueue = [];
		bitgridSearch(0, 31, 0, 31, cell => {
			if (cell.type === CELL_TYPE_PELLET && ++i % fraction >= 1) removalQueue.push(cell);
		});
		for (const pellet of removalQueue) bitgridRemove(pellet);
		pellets -= removalQueue.length;
	}

	for (; viruses < settings.virusMinCount; ++viruses) {
		const [x, y] = safeSpawnPos(settings.virusSize);
		add({ type: CELL_TYPE_VIRUS, x, y, r: settings.virusSize, rgb: 0x33ff33 });
	}

	for (let i = 0, l = boostingCells.length; i < l; ++i) {
		const cell = boostingCells[i];
		cell.x += cell.boostUnitX * cell.boostMagnitude / 9;
		cell.y += cell.boostUnitY * cell.boostMagnitude / 9;
		cell.boostMagnitude *= 8 / 9;

		bounce(cell, true);
		cell.moved = now;
		encode(cell);
		bitgridUpdate(cell);
	}
	let j = 0; // remove non-boosting cells all at once
	for (let i = 0, l = boostingCells.length; i < l; ++i) {
		boostingCells[j] = boostingCells[i];
		if (boostingCells[i].boostMagnitude >= 1) ++j;
	}
	boostingCells.length = j;

	let eatL = 0;
	let rigidL = 0;
	const eat = worldEatArray;
	const rigid = worldRigidArray;
	for (let i = 0, l = boostingCells.length; i < l; ++i) {
		const cell = boostingCells[i];
		if (cell.type === CELL_TYPE_PLAYER) continue;
		bitgridSearch(cell.bgXmin, cell.bgXmax, cell.bgYmin, cell.bgYmax, otherCell => {
			if (cell === otherCell) return;
			else if (leftCollidesRight(cell, otherCell)) rigid[rigidL++] = cell, rigid[rigidL++] = otherCell;
			else if (leftEatsRight(cell, otherCell)) eat[eatL++] = cell, eat[eatL++] = otherCell;
			else if (leftEatsRight(otherCell, cell)) eat[eatL++] = otherCell, eat[eatL++] = cell;
		});
	}

	for (let i = 0, l = playerCells.length; i < l; ++i) {
		const cell = playerCells[i];
		const { owner } = cell;
		if (!owner.disconnectedAt) {
			let dx = owner.mouseX - cell.x;
			let dy = owner.mouseY - cell.y;
			let d = Math.hypot(dx, dy);
			if (d >= 1) {
				// no idea where -0.4396754 comes from
				const realDistance = Math.min(d, 88 * (cell.r ** -0.4396754)) * settings.playerMoveMult;
				cell.x += dx / d * realDistance;
				cell.y += dy / d * realDistance;
			}
		}

		cell.r -= cell.r * settings.playerDecayMult / 50;
		if (cell.r < settings.playerMinSize) cell.r = settings.playerMinSize;

		if (cell.r > settings.playerMaxSize) {
			const overflow = Math.ceil(cell.r * cell.r / (settings.playerMaxSize * settings.playerMaxSize));
			const splitCellCount = Math.max(Math.min(overflow, settings.playerMaxCells - cell.owner.owned.size), 0);
			const splitSize = Math.min(Math.sqrt(cell.r * cell.r / splitCellCount), settings.playerMaxSize);
			for (let i = 1; i < splitCellCount; ++i) {
				const angle = Math.random() * 2 * Math.PI;
				const boostUnitX = Math.cos(angle);
				const boostUnitY = Math.sin(angle);
				const newCell = add({
					type: CELL_TYPE_PLAYER,
					x: cell.x + settings.playerSplitDistance * boostUnitX,
					y: cell.y + settings.playerSplitDistance * boostUnitY,
					r: splitSize, rgb: cell.rgb, owner: cell.owner,
					boostUnitX, boostUnitY, boostMagnitude: settings.playerSplitBoost,
				});
				cell.owner.owned.add(newCell);
				boostingCells.push(newCell);
				playerCells.push(newCell);
			}
			cell.r = splitSize;
		}

		bounce(cell, false);
		cell.moved = now;
		encode(cell);
		bitgridUpdate(cell);
	}

	// OgarII uses playerCells.unshift() for insertions and iterates 0 -> len.
	// but it's much faster to keep the list reversed, use playerCells.push() for insertions, and iterate len -> 0.
	for (let i = playerCells.length - 1; i >= 0; --i) {
		const cell = playerCells[i];
		bitgridSearch(cell.bgXmin, cell.bgXmax, cell.bgYmin, cell.bgYmax, otherCell => {
			if (cell === otherCell) return;
			else if (leftCollidesRight(cell, otherCell)) rigid[rigidL++] = cell, rigid[rigidL++] = otherCell;
			else if (leftEatsRight(cell, otherCell)) eat[eatL++] = cell, eat[eatL++] = otherCell;
			else if (leftEatsRight(otherCell, cell)) eat[eatL++] = otherCell, eat[eatL++] = cell;
		});
	}

	tickMeasurement('cells1');

	for (let i = 0; i < rigidL; i += 2) {
		const a = rigid[i];
		const b = rigid[i + 1];

		let dx = b.x - a.x;
		let dy = b.y - a.y;
		let d = Math.hypot(dx, dy);
		const extraSpace = a.r + b.r - d;
		if (extraSpace <= 0) continue;
		if (d === 0) d = 1, dx = 1, dy = 0;

		const massA = a.r * a.r;
		const massB = b.r * b.r;
		const factorA = massB / (massA + massB);
		const factorB = massA / (massA + massB);
		a.x -= dx / d * extraSpace * factorA;
		a.y -= dy / d * extraSpace * factorA;
		b.x += dx / d * extraSpace * factorB;
		b.y += dy / d * extraSpace * factorB;

		bounce(a, false); bounce(b, false);
		a.moved = b.moved = now;
		encode(a); encode(b);
		bitgridUpdate(a); bitgridUpdate(b); // TODO maybe defer this if possible
	}

	for (let i = 0; i < eatL; i += 2) {
		const a = eat[i];
		const b = eat[i + 1];
		if (a.dead || b.dead) continue;

		if (a.type === CELL_TYPE_VIRUS && b.type === CELL_TYPE_EJECT && viruses >= settings.virusMaxCount) continue; 

		const dx = b.x - a.x;
		const dy = b.y - a.y;
		const d = Math.hypot(dx, dy);
		if (d > a.r - b.r / settings.worldOverlapEatDiv) continue;

		a.r = Math.sqrt(a.r * a.r + b.r * b.r);
		a.moved = now;

		if (a.type === CELL_TYPE_VIRUS && b.type === CELL_TYPE_EJECT && ++a.fed >= settings.virusFeedTimes) {
			a.fed = 0;
			a.r = settings.virusSize;
			const angle = Math.atan2(b.boostUnitY, b.boostUnitX);
			const virus = add({
				type: CELL_TYPE_VIRUS, x: a.x, y: a.y, r: settings.virusSize, rgb: 0x33ff33,
				boostUnitX: Math.cos(angle), boostUnitY: Math.sin(angle), boostMagnitude: settings.virusSplitBoost,
			});
			boostingCells.push(virus);
			++viruses;
		}

		if (b.type === CELL_TYPE_VIRUS && a.type === CELL_TYPE_PLAYER) {
			let cellsLeft = settings.playerMaxCells - a.owner.owned.size;
			if (cellsLeft > 0) {
				const splitMinMass = settings.playerMinSplitSize * settings.playerMinSplitSize;
				let mass = a.r * a.r;
				// just gonna copy this blindly because this logic is really weird
				if (mass / cellsLeft < splitMinMass) {
					let amount = 2, perPiece = 1;
					while ((perPiece = mass / (amount + 1)) >= splitMinMass && amount * 2 <= cellsLeft) {
						amount *= 2;
					}
					const radius = Math.sqrt(perPiece);
					for (let i = 0; i < amount; ++i) {
						const angle = Math.random() * 2 * Math.PI;
						const boostUnitX = Math.cos(angle);
						const boostUnitY = Math.sin(angle);
						const newCell = add({
							type: CELL_TYPE_PLAYER,
							x: a.x + settings.playerSplitDistance * boostUnitX,
							y: a.y + settings.playerSplitDistance * boostUnitY,
							r: radius, rgb: a.rgb, owner: a.owner,
							boostUnitX, boostUnitY, boostMagnitude: settings.playerSplitBoost,
						});
						a.owner.owned.add(newCell);
						boostingCells.push(newCell);
						playerCells.push(newCell);
					}
					a.r = radius;
				} else {
					const radii = [];
					let nextMass = mass / 2;
					a.r = Math.sqrt(mass / 2);
					let massLeft = mass / 2;
					while (cellsLeft > 0) {
						if (nextMass / cellsLeft < splitMinMass) break;
						while (nextMass >= massLeft && cellsLeft > 1)
							nextMass /= 2;
						radii.push(Math.sqrt(nextMass));
						massLeft -= nextMass;
						--cellsLeft;
					}
					const radius = Math.sqrt(massLeft / cellsLeft);
					for (let i = 0; i < cellsLeft; ++i) radii.push(radius);

					for (let i = 0, l = radii.length; i < l; ++i) {
						const angle = Math.random() * 2 * Math.PI;
						const boostUnitX = Math.cos(angle);
						const boostUnitY = Math.sin(angle);
						const newCell = add({
							type: CELL_TYPE_PLAYER,
							x: a.x + settings.playerSplitDistance * boostUnitX,
							y: a.y + settings.playerSplitDistance * boostUnitY,
							r: radii[i], rgb: a.rgb, owner: a.owner,
							boostUnitX, boostUnitY, boostMagnitude: settings.playerSplitBoost,
						});
						a.owner.owned.add(newCell);
						boostingCells.push(newCell);
						playerCells.push(newCell);
					}
				}
			}
		}
		encode(a);
		bitgridUpdate(a);

		b.dead = true;
		b.deadTo = a.id;
		remove(b);
	}

	eat.fill(undefined, 0, eatL); // set everything to undefined, but do not reduce the allocated size of the array
	rigid.fill(undefined, 0, rigidL);

	j = 0; // clean up dead boosting cells
	for (let i = 0, l = boostingCells.length; i < l; ++i) {
		boostingCells[j] = boostingCells[i];
		if (!boostingCells[i].dead) ++j;
	}
	boostingCells.length = j;

	j = 0; // clean up dead player cells
	for (let i = 0, l = playerCells.length; i < l; ++i) {
		playerCells[j] = playerCells[i];
		if (!playerCells[i].dead) ++j;
	}
	playerCells.length = j;

	tickMeasurement('cells2');

	// now update players
	// compile leaderboard, or at least find the largest player
	const leaderboard = [];
	let largestPlayer, largestPlayerMass = 0;
	if (now % 4 === 0) {
		for (const player of players) {
			if (player.minionCommander) continue;
			let mass = 0;
			for (const cell of player.owned) {
				mass += cell.r * cell.r;
			}
			if (mass) leaderboard.push({ player, mass });
		}
		leaderboard.sort((a, b) => b.mass - a.mass);
		largestPlayer = leaderboard[0]?.player;
		largestPlayerMass = leaderboard[0]?.mass || 0;
	} else {
		for (const player of players) {
			if (player.minionCommander) continue;
			let mass = 0;
			for (const cell of player.owned) mass += cell.r * cell.r;
			if (mass > largestPlayerMass) [largestPlayer, largestPlayerMass] = [player, mass];
		}
	}

	for (const player of players) {
		if (player.disconnectedAt) {
			if (player.state === PLAYER_STATE_PLAYING && now - player.disconnectedAt > settings.worldPlayerDisposeDelay) {
				j = 0; // remove player's cells
				for (let i = 0, l = playerCells.length; i < l; ++i) {
					playerCells[j] = playerCells[i];
					if (playerCells[j].owner !== player) ++j;
					else {
						playerCells[i].dead = true;
						bitgridRemove(playerCells[i]);
					}
				}
				playerCells.length = j;
				players.delete(player);
				player.owned.clear();
				player.state = PLAYER_STATE_IDLE;
			} else if (player.state !== PLAYER_STATE_PLAYING) {
				players.delete(player);
				player.state = PLAYER_STATE_IDLE;
			}
		} else {
			// split
			for (let i = 0; i < player.splits; ++i) {
				for (const cell of Array.from(player.owned)) {
					if (player.owned.size >= settings.playerMaxCells) break;
					if (cell.r < settings.playerMinSplitSize) continue;

					let dx = player.mouseX - cell.x;
					let dy = player.mouseY - cell.y;
					let d = Math.hypot(dx, dy);
					if (d < 1) d = 1, dx = 1, dy = 0;

					const newCell = add({
						type: CELL_TYPE_PLAYER,
						x: cell.x + settings.playerSplitDistance * dx / d,
						y: cell.y + settings.playerSplitDistance * dy / d,
						r: cell.r / SQRT2, rgb: cell.rgb, owner: cell.owner,
						boostUnitX: dx / d, boostUnitY: dy / d, boostMagnitude: settings.playerSplitBoost,
					});
					cell.owner.owned.add(newCell);
					boostingCells.push(newCell);
					playerCells.push(newCell);

					cell.r /= SQRT2;
					cell.moved = now;
					encode(cell);
					bitgridUpdate(cell);
				}
			}
			player.splits = 0;

			// eject
			if (player.w && now - player.lastW >= settings.playerEjectDelay) {
				for (const cell of player.owned) {
					if (cell.r < settings.playerMinEjectSize) continue;
					let dx = player.mouseX - cell.x;
					let dy = player.mouseY - cell.y;
					let d = Math.hypot(dx, dy);
					if (d < 1) d = 1, dx = 1, dy = 0;

					const angle = Math.atan2(dy, dx) + (Math.random() * 2 - 1) * settings.ejectDispersion;
					const eject = add({
						type: CELL_TYPE_EJECT, x: cell.x + cell.r * dx / d, y: cell.y + cell.r * dy / d,
						r: settings.ejectedSize, rgb: cell.rgb,
						boostUnitX: Math.cos(angle), boostUnitY: Math.sin(angle),
						boostMagnitude: settings.ejectedCellBoost,
					});
					boostingCells.push(eject);

					cell.r = Math.sqrt(cell.r * cell.r - settings.ejectingLoss * settings.ejectingLoss);
					cell.moved = now;
					encode(cell);
					bitgridUpdate(cell);
				}
				player.lastW = now;
				player.w = false;
			}

			// spawn request
			if (!player.owned.size) {
				if (!player.spawn && player.state === PLAYER_STATE_PLAYING) player.state = PLAYER_STATE_IDLE;
				else if (player.spawn && player.state !== PLAYER_STATE_LIMBO) {
					if (player.spawn.spectating) player.state = PLAYER_STATE_SPECTATE;
					else {
						player.nameU8 = player.spawn.nameU8;
						player.skinU8 = player.spawn.skinU8;
						player.sub = player.spawn.sub;
						player.state = PLAYER_STATE_PLAYING;

						const spawnSize = player.minionCommander ? settings.minionSpawnSize : settings.playerSpawnSize;
						const [x, y] = safeSpawnPos(spawnSize);
						const rgb = player.rgb = randomColors[~~(Math.random() * 256 * 6)];
						const cell = add({ type: CELL_TYPE_PLAYER, x, y, r: spawnSize, rgb, owner: player });
						player.owned.add(cell);
						playerCells.push(cell);
					}
				}
			}
			if (player.spawn) player.spawn = undefined; // it should have been processed by now

			// q press, and update state
			if (player.q) {
				if (player.state === PLAYER_STATE_ROAM || player.state === PLAYER_STATE_IDLE) player.state = PLAYER_STATE_SPECTATE;
				else if (player.state === PLAYER_STATE_SPECTATE) player.state = PLAYER_STATE_ROAM;
				player.q = false;
			}
			if (player.state === PLAYER_STATE_SPECTATE && !largestPlayer) player.state = PLAYER_STATE_ROAM;

			// update view area
			if (player.state === PLAYER_STATE_PLAYING) {
				let x = 0, y = 0, r = 0;
				for (const cell of player.owned) {
					x += cell.x;
					y += cell.y;
					r += cell.r;
				}
				player.camera = {
					x: (x / player.owned.size) || 0,
					y: (y / player.owned.size) || 0,
					scale: Math.min(64 / r, 1) ** 0.4,
				};
			} else if (player.state === PLAYER_STATE_ROAM) {
				const dx = player.mouseX - player.camera.x;
				const dy = player.mouseY - player.camera.y;
				const d = Math.hypot(dx, dy);
				const distance = Math.min(d, settings.playerRoamSpeed);
				if (distance >= 1) {
					player.camera = {
						x: Math.min(Math.max(player.camera.x + dx / d * distance, -settings.worldMapW), settings.worldMapW),
						y: Math.min(Math.max(player.camera.y + dy / d * distance, -settings.worldMapW), settings.worldMapW),
						scale: settings.playerRoamViewScale,
					};
				}
			}
		}
	}

	// do this afterwards, to make sure largestPlayer.camera is up-to-date
	for (const player of players) {
		if (player.state === PLAYER_STATE_SPECTATE) player.camera = largestPlayer.camera;
	}

	// update stats, this will also be used for minions
	let playingExternal = 0;
	let playingInternal = 0;
	let spectating = 0;
	for (const player of players) {
		if (player.minionCommander || player.bot) ++playingInternal;
		else if (player.state === PLAYER_STATE_PLAYING) ++playingExternal;
		else if (player.state === PLAYER_STATE_ROAM || player.state === PLAYER_STATE_SPECTATE) ++spectating;
	}

	// now, update minions
	let targetMinionsPerPlayer = 0;
	if (settings.worldMinionsPerPlayer && settings.worldMaxMinions && playingExternal) {
		targetMinionsPerPlayer = Math.min(
			settings.worldMinionsPerPlayer,
			Math.ceil(settings.worldMaxMinions / playingExternal),
		);
	}

	const minionsPerPlayer = new Map();
	// remove extra minions
	for (const player of players) {
		if (!player.minionCommander) continue;
		let minions = minionsPerPlayer.get(player.minionCommander) || 0;
		if (minions > targetMinionsPerPlayer || player.minionCommander.state !== PLAYER_STATE_PLAYING) {
			player.disconnectedAt = -Infinity; // make sure its cells are immediately deleted
		} else {
			minionsPerPlayer.set(player.minionCommander, minions + 1);
		}
	}

	// add new minions
	for (const player of players) {
		if (player.minionCommander || player.bot) continue;
		if (player.state !== PLAYER_STATE_PLAYING) continue;
		let minions = minionsPerPlayer.get(player) || 0;
		for (; minions < targetMinionsPerPlayer; ++minions) {
			players.add({
				bot: false,
				camera: { x: 0, y: 0, scale: 1 },
				clanU8: EMPTY_STRING_U8,
				disconnectedAt: 0,
				lastW: 0,
				minionCommander: player,
				mouseX: 0,
				mouseY: 0,
				nameU8: EMPTY_STRING_U8,
				owned: new Set(),
				rgb: 0x7f7f7f,
				q: false,
				showClanmates: false,
				skinU8: EMPTY_STRING_U8,
				spawn: undefined,
				splits: 0,
				state: PLAYER_STATE_IDLE,
				sub: false,
				updated: now,
				visibleCells: new Set(),
				w: false,
			});
		}
	}

	// add/remove extra player bots
	let playerBots = 0;
	for (const player of players) {
		if (player.bot) {
			if (playerBots > settings.worldPlayerBotsPerWorld) player.disconnectedAt = -Infinity;
			else ++playerBots;
		}
	}

	for (; playerBots < settings.worldPlayerBotsPerWorld; ++playerBots) {
		players.add({
			bot: true,
			camera: { x: 0, y: 0, scale: 1 },
			clanU8: EMPTY_STRING_U8,
			disconnectedAt: 0,
			minionCommander: undefined,
			mouseX: 0,
			mouseY: 0,
			lastW: 0,
			nameU8: EMPTY_STRING_U8,
			owned: new Set(),
			rgb: 0x7f7f7f,
			q: false,
			showClanmates: false,
			skinU8: EMPTY_STRING_U8,
			spawn: undefined,
			splits: 0,
			state: PLAYER_STATE_IDLE,
			sub: false,
			updated: now,
			visibleCells: new Set(),
			w: false,
		});
	}

	tickMeasurement('cells3');

	// compile statistics
	let avgTickTime = 0;
	for (const frame of metricsMeasurements) avgTickTime += frame.time;
	const statsU8Partial = textEncoder.encode(JSON.stringify({
		limit: settings.listenerMaxConnections,
		internal: playingInternal, // might be outdated by one tick, but that's okay
		external: connections,
		playing: playingExternal,
		spectating,
		name: settings.serverName,
		gamemode: settings.serverGamemode,
		loadTime: avgTickTime / metricsMeasurements.length,
		uptime: ~~(performance.now() / 1000),
		// legacy
		mode: settings.serverGamemode,
		update: avgTickTime / metricsMeasurements.length,
		playersTotal: playingExternal + spectating,
		playersAlive: playingExternal,
		playersSpect: spectating,
		playersLimit: settings.listenerMaxConnections,
	}));
	statsU8 = new Uint8Array(statsU8Partial.length + 1);
	statsU8[0] = 0xfe;
	statsU8.set(statsU8Partial, 1);

	// #2 update connections
	const newVisibleCells = new Map();
	for (const player of players) {
		if (player.disconnectedAt) continue;
		if (now - player.updated >= settings.listenerMaxClientDormancy / 40) {
			if (!player.bot && !player.minionCommander) player.ws.close();
			else player.disconnectedAt = -Infinity;
			continue;
		}

		if (player.state === PLAYER_STATE_LIMBO) {
			player.state = PLAYER_STATE_IDLE;
			player.spawn = undefined; // but make sure matchmaker enqueue is done first
			player.w = player.q = false;
			player.splits = 0;
			continue;
		}

		if (player.minionCommander) {
			player.mouseX = player.minionCommander.mouseX;
			player.mouseY = player.minionCommander.mouseY;
			player.splits = 1;
			if (!player.owned.size) player.spawn = MINION_SPAWN;
			player.updated = now;
			continue;
		}

		if (newVisibleCells.has(player.camera)) continue;

		// this is not exact; if you're spectating #1, but they have some cells beyond their camera range, you aren't
		// supposed to be able to see them. but it doesn't really matter here, it's all in the name of performance
		let visibleCells;
		if (player.camera === largestPlayer?.camera) visibleCells = new Set(largestPlayer.owned);
		else visibleCells = new Set(player.owned);

		let cameraWidth = 1920 / player.camera.scale / 2 * settings.playerViewScaleMult;
		let cameraHeight = 1080 / player.camera.scale / 2 * settings.playerViewScaleMult;
		if (player.bot) {
			cameraWidth /= 3;
			cameraHeight /= 3;
		}
		const cameraXmin = player.camera.x - cameraWidth;
		const cameraXmax = player.camera.x + cameraWidth;
		const cameraYmin = player.camera.y - cameraHeight;
		const cameraYmax = player.camera.y + cameraHeight;
		const xmin = ~~(Math.max(cameraXmin + settings.worldMapW, 0) / BITGRID_TILE_SIZE);
		const xmax = ~~(Math.min(cameraXmax + settings.worldMapW, settings.worldMapW * 2) / BITGRID_TILE_SIZE);
		const ymin = ~~(Math.max(cameraYmin + settings.worldMapH, 0) / BITGRID_TILE_SIZE);
		const ymax = ~~(Math.min(cameraYmax + settings.worldMapH, settings.worldMapH * 2) / BITGRID_TILE_SIZE);
		bitgridSearch(xmin, xmax, ymin, ymax, cell => {
			if (cameraXmin <= cell.x + cell.r && cell.x - cell.r <= cameraXmax
				&& cameraYmin <= cell.y + cell.r && cell.y - cell.r <= cameraYmax) {
				visibleCells.add(cell);
			}
		});

		newVisibleCells.set(player.camera, visibleCells);
	}

	tickMeasurement('con1');

	let maxEatL = 0, maxAddL = 0, maxUpdL = 0, maxDelL = 0;
	con2PlayerLoop: for (const player of players) {
		if (player.disconnectedAt || player.minionCommander || player.bot) continue;

		const visibleCells = newVisibleCells.get(player.camera);
		if (!visibleCells) continue; // could happen if the player was just in limbo

		const oldVisibleCells = player.visibleCells;

		// leaderboard (must be recomputed for every player, because of "myPosition")
		let o = 0;
		if (now % 4 === 0) {
			writerU8[o++] = 0x31;
			const length = Math.min(leaderboard.length, 10);
			const myPosition = leaderboard.findIndex(entry => entry.player === player) || 0; // 0 if not found

			(writerDat.setUint32(o, length, true), o += 4);
			for (let i = 0; i < length; ++i) {
				const { player: lbPlayer } = leaderboard[i];
				(writerDat.setUint32(o, lbPlayer === player ? 1 : 0, true), o += 4);
				(writerU8.set(lbPlayer.nameU8, o), o += lbPlayer.nameU8.length);
				(writerDat.setUint32(o, myPosition + 1, true), o += 4); // sigmally
				(writerDat.setUint32(o, lbPlayer.sub ? 1 : 0, true), o += 4); // sigmally
			}

			void player.ws.send(writerU8.subarray(0, o), true);
		}

		// the new Set.prototype.difference and .intersection functions are only faster if the two sets are very
		// disjoint, but usually they aren't (a player can't move that far between ticks)
		// also, they were only added in node.js 22, which is quite recent, so better to stick with the old method
		const newOwned = [];
		let eatL = 0, addL = 0, updL = 0, delL = 0;
		const eat = worldPacketEatArray;
		const add = worldPacketAddArray;
		const upd = worldPacketUpdArray;
		const del = worldPacketDelArray;
		for (const cell of visibleCells) {
			if (oldVisibleCells.has(cell)) {
				if (cell.moved === now) upd[updL++] = cell.moveU8;
			} else {
				if (cell.owner === player) newOwned.push(cell.id);
				add[addL++] = cell.firstU8;
			}
		}
		for (const cell of oldVisibleCells) {
			if (visibleCells.has(cell)) continue;
			if (cell.deadTo) eat[eatL++] = cell;
			else del[delL++] = cell; // sigmally: non-sigmally clients require the cell to be in both eat and del
		}

		if (eatL > maxEatL) maxEatL = eatL;
		if (addL > maxAddL) maxAddL = addL;
		if (updL > maxUpdL) maxUpdL = updL;
		if (delL > maxDelL) maxDelL = delL;

		if (newOwned.length) {
			writerU8[0] = 0x20;
			for (let i = 0; i < newOwned.length; ++i) {
				writerDat.setUint32(1, newOwned[i], true);
				if (player.ws.send(writerU8.subarray(0, 5), true) !== 1) {
					continue con2PlayerLoop;
				}
			}
		}

		if (player.state === PLAYER_STATE_ROAM || player.state === PLAYER_STATE_SPECTATE) {
			writerU8[0] = 0x11;
			writerDat.setFloat32(1, player.camera.x, true);
			writerDat.setFloat32(5, player.camera.y, true);
			writerDat.setFloat32(9, player.camera.scale, true);
			void player.ws.send(writerU8.subarray(0, 13), true);
		}

		// update packet
		o = 0;
		writerU8[o++] = 0x10;
		(writerDat.setUint16(o, eatL, true), o += 2);
		for (let i = 0; i < eatL; ++i) {
			(writerDat.setUint32(o, eat[i].deadTo, true), o += 4);
			(writerDat.setUint32(o, eat[i].id, true), o += 4);
		}

		for (let i = 0; i < addL; ++i) (writerU8.set(add[i], o), o += add[i].length);
		for (let i = 0; i < updL; ++i) (writerU8.set(upd[i], o), o += upd[i].length);
		(writerDat.setUint32(o, 0, true), o += 4);

		(writerDat.setUint16(o, delL, true), o += 2);
		for (let i = 0; i < delL; ++i) (writerDat.setUint32(o, del[i].id, true), o += 4);

		if (player.ws.send(writerU8.subarray(0, o), true) === 1) {
			// only update visible cells if there is no backpressure
			player.visibleCells = visibleCells;
		}
	}

	// "clear" the array, but do not reduce the allocated size of the array
	worldPacketEatArray.fill(undefined, 0, maxEatL);
	worldPacketAddArray.fill(undefined, 0, maxAddL);
	worldPacketUpdArray.fill(undefined, 0, maxUpdL);
	worldPacketDelArray.fill(undefined, 0, maxDelL);

	tickMeasurement('con2');

	for (const player of players) {
		if (!player.bot || player.disconnectedAt) continue;

		const visibleCells = newVisibleCells.get(player.camera);

		player.updated = now;
		// copied straight from OgarII, just like everything else, not my logic
		let ai = playerBotAi.get(player);
		if (!ai) playerBotAi.set(player, ai = { splitCooldownTicks: 0, target: undefined });

		if (ai.splitCooldownTicks) --ai.splitCooldownTicks;
		else ai.target = undefined;

		if (player.state !== PLAYER_STATE_PLAYING) {
			player.spawn = {
				nameU8: PLAYER_BOT_NAMES_U8[~~(Math.random() * PLAYER_BOT_NAMES_U8.length)],
				skinU8: PLAYER_BOT_SKINS_U8[~~(Math.random() * PLAYER_BOT_SKINS_U8.length)],
				spectating: false,
				sub: false,
			};
			continue;
		}

		let leader;
		for (const cell of player.owned) {
			if (!leader || cell.r > leader.r) leader = cell;
		}
		if (!leader) continue;

		if (ai.target) {
			if (ai.target.dead || leader.r <= ai.target.r * WORLD_EAT_MULT) {
				ai.target = undefined;
			} else {
				player.mouseX = ai.target.x;
				player.mouseY = ai.target.y;
				continue;
			}
		}

		let mouseX = 0;
		let mouseY = 0;
		let bestPrey = undefined;
		let splitKillObstacleNearby = false;

		const splitDistance = Math.max(leader.r / SQRT2, settings.playerSplitBoost); 

		for (const cell of visibleCells) {
			const dx = cell.x - leader.x;
			const dy = cell.y - leader.y;
			const dSplit = Math.max(1, Math.hypot(dx, dy));
			const d = Math.max(1, dSplit - cell.r - leader.r);
			let influence = 0;

			if (cell.type === CELL_TYPE_PELLET) {
				influence = 1;
			} else {
				const truncatedInfluence = Math.log10(cell.r * cell.r);
				const canSplitKill = leader.r / SQRT2 > cell.r * WORLD_EAT_MULT
					&& d - splitDistance <= leader.r - cell.r * WORLD_EAT_OVERLAP_MULT;
				const canEat = leader.r >= cell.r * WORLD_EAT_MULT;
				if (cell.type === CELL_TYPE_PLAYER) {
					if (cell.owner !== player) {
						if (canEat) {
							influence = truncatedInfluence;
							if (canSplitKill && (!bestPrey || cell.r > bestPrey.r)) bestPrey = cell;
						} else {
							if (cell.r < leader.r * WORLD_EAT_MULT) influence = -1;
							else influence = -truncatedInfluence * player.owned.size;
							splitKillObstacleNearby = true;
						}
					}
				} else if (cell.type === CELL_TYPE_VIRUS) {
					if (player.owned.size >= settings.playerMaxCells) influence = truncatedInfluence;
					else if (canEat) {
						influence = -1 * player.owned.size;
						if (canSplitKill) splitKillObstacleNearby = true;
					}
				} else if (cell.type === CELL_TYPE_EJECT) {
					influence = truncatedInfluence * player.owned.size;
				}
			}

			if (d === 0) d = 1;
			mouseX += dx / d * influence / d;
			mouseY += dy / d * influence / d;
		}

		if (player.owned.size <= 2 && !splitKillObstacleNearby && ai.splitCooldownTicks <= 0
			&& bestPrey && bestPrey.r * 2 > leader.r) {
			ai.target = bestPrey;
			player.mouseX = bestPrey.x;
			player.mouseY = bestPrey.y;
			++player.splits;
			ai.splitCooldownTicks = 25;
		} else {
			const cameraWidth = 1920 / player.camera.scale / 2 * settings.playerViewScaleMult;
			const cameraHeight = 1080 / player.camera.scale / 2 * settings.playerViewScaleMult;
			const d = Math.hypot(mouseX, mouseY);
			if (d >= 0.001) {
				player.mouseX = leader.x + mouseX / d * cameraWidth;
				player.mouseY = leader.y + mouseY / d * cameraHeight;
			} else {
				// clockwise rotation around the map if it can't find anything
				player.mouseX = leader.y;
				player.mouseY = -leader.x;
			}
		}
	}

	tickMeasurement('con3');

	// #3 update matchmaker
	// #4 update gamemode-specific

	const elapsed = performance.now() - start;
	metricsMeasurements[now % 100] = { points: framePoints, time: elapsed };
	++now;
	setTimeout(worldTick, Math.max(40 - elapsed, 0));
};
worldTick();

//========== networking ================================================================================================

const SIG_VERSION_STRING_U8 = textEncoder.encode('SIG 0.0.1\0');
// SIG 0.0.1\0, then integers 0-255 (don't bother with opcode shuffling)
const SIG_HANDSHAKE_U8 = new Uint8Array(SIG_VERSION_STRING_U8.length + 256);
SIG_HANDSHAKE_U8.set(SIG_VERSION_STRING_U8);
for (let i = 0, o = SIG_VERSION_STRING_U8.length; i < 256; ++i, ++o) SIG_HANDSHAKE_U8[o] = i;

const BORDER_UPDATE_PACKET_DAT = new DataView(new ArrayBuffer(33));
BORDER_UPDATE_PACKET_DAT.setUint8(0, 0x40);
BORDER_UPDATE_PACKET_DAT.setFloat64(1, -settings.worldMapW, true);
BORDER_UPDATE_PACKET_DAT.setFloat64(9, -settings.worldMapH, true);
BORDER_UPDATE_PACKET_DAT.setFloat64(17, settings.worldMapW, true);
BORDER_UPDATE_PACKET_DAT.setFloat64(25, settings.worldMapH, true);
const BORDER_UPDATE_PACKET_U8 = new Uint8Array(BORDER_UPDATE_PACKET_DAT.buffer);

const SERVER_NAME_U8 = encodeUtf8AsU8('Server');
const SPECTATOR_NAME_U8 = encodeUtf8AsU8('Spectator');
// caching utf8 probably is not that necessary, but it's cool, so why not
const serverMessageCache = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15].map(x => undefined);
const messagePacketU8 = (flags, color, nameU8, messageU8) => {
	let o = 0;
	writerU8[o++] = 0x63; // chat opcode
	writerU8[o++] = flags;
	(writerDat.setUint32(o, color, true), o += 3);
	(writerU8.set(nameU8, o), o += nameU8.length);
	(writerU8.set(messageU8, o), o += messageU8.length);
	return writerU8.subarray(0, o);
};

let cliChatMuted = false;

uws.App()
	.ws('/*', {
		idleTimeout: 60,
		maxBackpressure: 64 * 1024,
		maxPayloadLength: 512,
		sendPingsAutomatically: false,
		upgrade: (res, req, context) => {
			// early destroy, before upgrading the connection
			if (connections > settings.listenerMaxConnections) res.close();
			else {
				res.upgrade({},
					req.getHeader('sec-websocket-key'),
					req.getHeader('sec-websocket-protocol'),
					req.getHeader('sec-websocket-extensions'),
					context);
			}
		},
		open: client => {
			if (++connections > settings.listenerMaxConnections) client.close();
		},
		close: client => {
			--connections;
			const player = client.getUserData().player;
			if (player) {
				player.disconnectedAt = now;
				player.ws = undefined;
			}
		},
		message: (client, buf) => {
			const player = client.getUserData().player;
			const dat = new DataView(buf);
			const u8 = new Uint8Array(buf);
			if (!dat.byteLength) return client.end(1009, 'Unexpected message size');
			if (!player) {
				if (u8.length !== SIG_VERSION_STRING_U8.length) return client.end(1003, 'Ambiguous protocol');
				for (let i = 0; i < u8.length; ++i) {
					if (u8[i] !== SIG_VERSION_STRING_U8[i]) return client.end(1003, 'Ambiguous protocol');
				}

				const newPlayer = {
					bot: false,
					camera: { x: 0, y: 0, scale: 1 },
					chatAt: now,
					clanU8: EMPTY_STRING_U8,
					disconnectedAt: 0,
					lastW: 0,
					minionCommander: undefined,
					mouseX: 0,
					mouseY: 0,
					nameU8: EMPTY_STRING_U8,
					owned: new Set(),
					q: false,
					rgb: 0x7f7f7f,
					showClanmates: false,
					skinU8: EMPTY_STRING_U8,
					spawn: undefined,
					splits: 0,
					state: PLAYER_STATE_IDLE,
					sub: false,
					updated: now,
					visibleCells: new Set(),
					w: false,
					ws: client,
				};
				players.add(newPlayer);
				client.getUserData().player = newPlayer;

				client.cork(() => { // TODO am i corking correctly?
					void client.send(SIG_HANDSHAKE_U8, true);
					void client.send(BORDER_UPDATE_PACKET_U8, true);
				});
				return;
			}

			player.updated = now;

			let o = 0;
			const readUtf8 = () => { // null-terminated utf8 string
				let start = o;
				while (o < u8.length && u8[o]) ++o;
				return textDecoder.decode(u8.subarray(start, o));
			};

			const opcode = u8[o++];
			if (opcode === 0) {
				let body;
				try {
					body = JSON.parse(readUtf8());
				} catch (err) {
					console.error(err);
					return client.end(1003, 'Unexpected message format');
				}

				if (typeof body !== 'object' || typeof body.name !== 'string'
					|| (body.skin && typeof body.skin !== 'string')
					|| (body.clan && typeof body.clan !== 'string')) {
					return client.end(1003, 'Unexpected message format');
				}

				const spectating = body.state ==/*=*/ 2;
				if (!spectating && settings.serverPassword && settings.serverPassword !== body.password) {
					void client.send(new Uint8Array([0xb4]), true); // password prompt
					return;
				}

				player.spawn = {
					nameU8: encodeUtf8AsU8(body.name.substring(0, 64)),
					// low limit, to prevent accessing things that aren't skins
					skinU8: encodeUtf8AsU8(body.skin ? body.skin.substring(0, 20) : ''),
					spectating,
					sub: !!body.sub,
				};
				player.clan = encodeUtf8AsU8(body.clan ? body.clan.substring(0, 32) : '');
			} else if (opcode === 0x10) {
				if (dat.byteLength === 13) {
					player.mouseX = dat.getInt32(o, true);
					player.mouseY = dat.getInt32(o + 4, true);
				} else if (dat.byteLength === 9) { // no one actually uses this but it's supported
					player.mouseX = dat.getInt16(o, true);
					player.mouseY = dat.getInt16(o + 2, true);
				} else if (dat.byteLength === 21) {
					player.mouseX = ~~dat.getFloat64(o, true);
					player.mouseY = ~~dat.getFloat64(o + 8, true);
				} else client.end(1003, 'Unexpected message format');
			} else if (opcode === 0x11) ++player.splits;
			else if (opcode === 0x12) player.q = true;
			else if (opcode === 0x13) player.q = false;
			else if (opcode === 0x15) player.w = true;
			else if (opcode === 0x63) {
				if (dat.byteLength < 2) return client.end(1003, 'Bad message format');
				++o; // skip flags altogether
				const message = readUtf8().trim();
				if (message[0] === '/' && message.length >= 2) {
					let [command, ...args] = message.split(' ');
					command = command.toLowerCase();
					const serverMessage = (cacheId, msg) => {
						void client.send(messagePacketU8(0x80, 0xc03f3f, SERVER_NAME_U8, serverMessageCache[cacheId] ??= encodeUtf8AsU8(msg)), true);
					}
					if (command === '/help') {
						serverMessage(0, 'available commands:');
						serverMessage(1, 'id - get your id');
						serverMessage(2, 'worldid - get your world\'s id');
						serverMessage(3, 'leaveworld - leave your world');
						serverMessage(4, 'joinworld <id> - try to join a world');
					} else if (command === '/id') {
						serverMessage(5, 'your ID is 0');
					} else if (command === '/worldid') {
						if (player.state === PLAYER_STATE_LIMBO) serverMessage(6, 'you\'re not in a world');
						else serverMessage(7, 'your world ID is 1');
					} else if (command === '/leaveworld') {
						if (player.state === PLAYER_STATE_LIMBO) return serverMessage(8, 'you\'re not in a world');

						let score = 0;
						for (const cell of player.owned) {
							score += cell.r * cell.r / 100;
						}
						if (score >= 5500) return serverMessage(9, 'you have >5500 score');

						player.state = PLAYER_STATE_LIMBO;
						for (const cell of player.owned) {
							cell.dead = true;
							bitgridRemove(cell);
						}
						player.owned.clear();
						
						let j = 0;
						for (let i = 0, l = playerCells.length; i < l; ++i) {
							playerCells[j] = playerCells[i];
							if (playerCells[i].owner !== player) ++j;
						}
						playerCells.length = j;

						j = 0;
						for (let i = 0, l = boostingCells.length; i < l; ++i) {
							boostingCells[j] = boostingCells[i];
							if (boostingCells[i].owner !== player) ++j;
						}
						boostingCells.length = j;

						void client.send(new Uint8Array([0x12]), true); // world reset
					} else if (command === '/joinworld') {
						// just assume the argument is 1
						if (player.state !== PLAYER_STATE_LIMBO) return serverMessage(10, 'you\'re already in a world');
						player.state = PLAYER_STATE_IDLE;
					} else {
						serverMessage(11, 'unknown command, execute /help for the list of commands');
					}

					return;
				}

				if (now - player.chatAt < 5) return; // no cooldown on commands (respawns), but slow down chats
				player.chatAt = now;
				const trimmed = message.substring(0, 32);
				const packet = messagePacketU8(
					0,
					player.rgb,
					player.nameU8 === EMPTY_STRING_U8 ? SPECTATOR_NAME : player.nameU8,
					encodeUtf8AsU8(trimmed),
				);
				for (const otherPlayer of players) {
					if (otherPlayer.state !== PLAYER_STATE_LIMBO && otherPlayer.ws)
						void otherPlayer.ws.send(packet, true);
				}
				// TODO there should be a better way to print chat messages
				if (!cliChatMuted) console.log(`  [${textDecoder.decode(player.nameU8)}] ${trimmed}`);
			} else if (opcode === 0xfe) {
				// stats
				if (player.state === PLAYER_STATE_LIMBO) return;
				void client.send(statsU8, true);
			}
		},
	})
	.listen(settings.listeningPort, () => console.log(`Listening on port ${settings.listeningPort}`));

const commandStream = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    terminal: true,
    prompt: "",
    historySize: 64,
    removeHistoryDuplicates: true
});

const ask = input => {
	input = input.trim();
	if (input) {
		const args = input.split(' ');
		const command = args.shift().toLowerCase();
		if (command === 'exit') {
			process.exit(0);
		} else if (command === 'help') {
			console.log('exit - calls process.exit(0)');
			console.log('help - show this help screen');
			console.log('mute - stop showing chat on the command line');
			console.log('players - shows a list of all real player and their names');
			console.log('safeexit - calls process.exit(0) as soon as there are 0 players playing');
			console.log('setting <name> <value> - changes a setting to a different value, or shows the current value');
			console.log('snapshot - dumps a memory snapshot, this can take several seconds');
			console.log('stats - show server uptime, load, memory usage, and player counts');
			console.log('unmute - start showing chats again on the command line');
		} else if (command === 'mute') {
			cliChatMuted = true;
			console.log('chat now muted on the cli');
		} else if (command === 'players') {
			for (const player of players) {
				if (player.bot || player.minionCommander) continue;

				let stateName;
				if (player.state === PLAYER_STATE_IDLE) stateName = '----';
				else if (player.state === PLAYER_STATE_PLAYING) stateName = 'play';
				else if (player.state === PLAYER_STATE_ROAM) stateName = 'roam';
				else if (player.state === PLAYER_STATE_SPECTATE) stateName = 'spec';
				else stateName = 'xxxx';

				let mass = 0;
				for (const cell of player.owned) {
					mass += cell.r * cell.r / 100;
				}

				// TODO should not be decoding text all the time
				console.log(`- ${stateName} - ${~~mass} mass - ${textDecoder.decode(player.nameU8)}`);
			}
		} else if (command === 'safeexit') {
			console.log('server will be exited once all players leave');
			setInterval(() => {
				for (const player of players) {
					if (player.minionCommander || player.bot) continue;
					if (player.state === PLAYER_STATE_PLAYING) return;
				}
				process.exit(0);
			}, 5000);
		} else if (command === 'say') {
			// if using the server flag, then sigfixes will duplicate messages between tabs, so
			// don't send messages to tabs on the same IP address
			const packet = messagePacketU8(0x80, 0xc03f3f, SERVER_NAME_U8, encodeUtf8AsU8(args.join(' ')));
			const usedAddresses = new Set(); 
			for (const player of players) {
				if (player.state === PLAYER_STATE_LIMBO || !player.ws) continue;
				const address = textDecoder.decode(player.ws.getRemoteAddressAsText());
				if (usedAddresses.has(address)) continue;
				usedAddresses.add(address);
				void player.ws.send(packet, true);
			}
		} else if (command === 'setting') {
			if (args[0] in settings) {
				if (args[1]) {
					if (typeof settings[args[0]] !== 'number') console.log('setting is not a number');
					else {
						const numeric = Number(args[1]);
						if (Number.isNaN(numeric)) console.log('argument not a number');
						else {
							const old = settings[args[0]];
							settings[args[0]] = numeric;
							console.log(`${args[0]} : ${old} -> ${numeric}`);
						}
					}
				} else {
					console.log(`${args[0]} : ${settings[args[0]]}`);
				}
			}
		} else if (command === 'snapshot') {
			const start = performance.now();
			const path = require('v8').writeHeapSnapshot();
			console.log(`written in ${(performance.now() - start).toFixed(2)} ms to ${path}`);
		} else if (command === 'stats') {
			const averages = [];
			let avgTickTime = 0;
			for (const frame of metricsMeasurements) {
				for (let i = 0; i < frame.points.length; ++i) {
					averages[i] = (averages[i] ?? 0) + frame.points[i];
				}
				avgTickTime += frame.time;
			}
			avgTickTime /= metricsMeasurements.length;
			console.log(`load:   ${avgTickTime.toFixed(2)} ms / 40 ms (${(avgTickTime * 2.5).toFixed(2)}%)`);
			for (let i = 0; i < metricsPointsLabels.length; ++i) {
				console.log(`     -> ${(averages[i] / metricsMeasurements.length).toFixed(2)} ms (${metricsPointsLabels[i]})`);
			}

			const memory = process.memoryUsage();
			const pretty = value => {
				const units = ["B", "kiB", "MiB", "GiB", "TiB"]; let i = 0;
			    for (; i < units.length && value / 1024 > 1; i++)
			        value /= 1024;
			    return `${value.toFixed(1)} ${units[i]}`;
			};
			console.log(`memory: ${pretty(memory.heapUsed)} / ${pretty(memory.heapTotal)} / ${pretty(memory.rss)} / ${pretty(memory.external)}`);

			const uptimeValue = performance.now() / 1000;
			let uptime = `${~~(uptimeValue % 60)}s`;
			if (uptimeValue >= 60) uptime = `${~~(uptimeValue / 60 % 60)}m ${uptime}`;
			if (uptimeValue >= 3600) uptime = `${~~(uptimeValue / 3600 % 24)}h ${uptime}`;
			if (uptimeValue >= 86400) uptime = `${~~(uptimeValue / 86400)}d ${uptime}`;
			console.log(`uptime: ${uptime}`);

			let realPellets = 0, realViruses = 0, realEjects = 0, realPlayerCells = 0, realCells = 0;
			let playing = 0, spectating = 0, idle = 0, minions = 0, bots = 0;
			bitgridSearch(0, 31, 0, 31, cell => {
				++realCells;
				if (cell.type === CELL_TYPE_PELLET) ++realPellets;
				else if (cell.type === CELL_TYPE_PLAYER) ++realPlayerCells;
				else if (cell.type === CELL_TYPE_EJECT) ++realEjects;
				else if (cell.type === CELL_TYPE_VIRUS) ++realViruses;
			});
			for (const player of players) {
				if (player.minionCommander) ++minions;
				else if (player.bot) ++bots;
				else if (player.state === PLAYER_STATE_ROAM || player.state === PLAYER_STATE_SPECTATE) ++spectating;
				else if (player.state === PLAYER_STATE_PLAYING) ++playing;
				else ++idle;
			}
			console.log(`${realCells} cells - ${realPlayerCells} player cells, ${realPellets}(${pellets}) pellets, ${realEjects} ejects, ${realViruses}(${viruses}) viruses`);
			console.log(`${playing} playing - ${spectating} spectating - ${idle} idle - ${minions} minions - ${bots} bots`);
		} else if (command === 'unmute') {
			cliChatMuted = false;
			console.log('chat now unmuted on the cli');
		} else {
			console.log('unknown command');
		}
	}
	commandStream.question('@ ', ask);
};
commandStream.question('@ ', ask);

const log = fs.createWriteStream(`log-${new Date().toISOString()}.txt`);
setInterval(() => {
	const averages = [];
	let avgTickTime = 0;
	for (const frame of metricsMeasurements) {
		for (let i = 0; i < frame.points.length; ++i) {
			averages[i] = (averages[i] ?? 0) + frame.points[i];
		}
		avgTickTime += frame.time;
	}
	let realPellets = 0, realViruses = 0, realEjects = 0, realPlayerCells = 0, realCells = 0;
	let playing = 0, spectating = 0, idle = 0, minions = 0, bots = 0;
	bitgridSearch(0, 31, 0, 31, cell => {
		++realCells;
		if (cell.type === CELL_TYPE_PELLET) ++realPellets;
		else if (cell.type === CELL_TYPE_PLAYER) ++realPlayerCells;
		else if (cell.type === CELL_TYPE_EJECT) ++realEjects;
		else if (cell.type === CELL_TYPE_VIRUS) ++realViruses;
	});
	for (const player of players) {
		if (player.minionCommander) ++minions;
		else if (player.bot) ++bots;
		else if (player.state === PLAYER_STATE_ROAM || player.state === PLAYER_STATE_SPECTATE) ++spectating;
		else if (player.state === PLAYER_STATE_PLAYING) ++playing;
		else ++idle;
	}
	log.write(`${new Date().toISOString()} | ${averages.map(x => (x / metricsMeasurements.length).toFixed(2)).join(' -> ')} (${(avgTickTime / 25 * 2.5).toFixed(1)}% load) | ${playing} playing, ${spectating} spectating, ${idle} idle, ${minions} minions, ${bots} bots | ${realPellets}(${pellets}) pellets, ${realViruses}(${viruses}), ${realEjects} ejects, ${realPlayerCells} player cells, ${realCells} total cells\n`);
}, 15_000);

console.log(`server started in ${performance.now().toFixed(1)}ms`);
