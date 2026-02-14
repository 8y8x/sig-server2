'use strict';

const fs = require('node:fs');
const { WebSocketServer } = require('ws');

const settings = require('./settings.json');
const serverStartTime = performance.now(); // probably 0 most of the time, but i don't want to risk it

const EMPTY_BUFFER = Buffer.alloc(0);
const EMPTY_STRING = Buffer.from([0]);
const writer = Buffer.alloc(2 ** 22); // 4MB is more than enough, even for the most extreme cases

//========== bitgrid ===================================================================================================

// undefined behaviour occurs if a cell ever exists beyond the bitgrid, just keep it in mind
// (the width and height) get all messed up
const BITGRID_TILE_SIZE = Math.max(1250, (settings.mapWidth * 2 + 3000) / 32);
const bitgridTiles = [];
for (let i = 0; i < 1024; ++i) bitgridTiles.push(new Set());

const bitgridAdd = cell => {
	const xmin = ~~((cell.x + settings.mapWidth - cell.r) / BITGRID_TILE_SIZE);
	const xmax = ~~((cell.x + settings.mapWidth + cell.r) / BITGRID_TILE_SIZE);
	const ymin = ~~((cell.y + settings.mapHeight - cell.r) / BITGRID_TILE_SIZE);
	const ymax = ~~((cell.y + settings.mapHeight + cell.r) / BITGRID_TILE_SIZE);
	cell.bgXmin = xmin; cell.bgXmax = xmax; cell.bgYmin = ymin; cell.bgYmax = ymax;

	for (let x = xmin; x <= xmax; ++x) {
		for (let y = ymin; y <= ymax; ++y) {
			bitgridTiles[y * 32 + x].add(cell);
		}
	}
};

const bitgridUpdate = cell => {
	const { bgXmin, bgXmax, bgYmin, bgYmax } = cell;
	const xmin = ~~((cell.x + settings.mapWidth - cell.r) / BITGRID_TILE_SIZE);
	const xmax = ~~((cell.x + settings.mapWidth + cell.r) / BITGRID_TILE_SIZE);
	const ymin = ~~((cell.y + settings.mapHeight - cell.r) / BITGRID_TILE_SIZE);
	const ymax = ~~((cell.y + settings.mapHeight + cell.r) / BITGRID_TILE_SIZE);
	
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
	const { xmin, xmax, ymin, ymax } = cell;
	for (let x = xmin; x <= xmax; ++x) {
		for (let y = ymin; y <= ymax; ++y) {
			bitgridTiles[y * 32 + x].delete(cell);
		}
	}
};

const bitgridSearch = (xmin, xmax, ymin, ymax, cb) => {
	for (let x = xmin; x <= xmax; ++x) {
		for (let y = ymin; y <= ymax; ++y) {
			for (const cell of bitgridTiles[y * 32 + x]) {
				if (xmin <= cell.xmin && cell.xmin < x && ymin <= cell.ymin && cell.ymin < y) continue; // no duplicates
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
	clan: EMPTY_STRING,
	disconnectedAt: 0,
	minionCommander: undefined,
	mouseX: 0,
	mouseY: 0,
	name: EMPTY_STRING,
	owned: new Set(),
	q: false,
	showClanmates: false,
	skin: EMPTY_STRING,
	spawn: undefined,
	splits: 0,
	state: PLAYER_STATE_IDLE,
	sub: false,
	updated: -Infinity,
	visibleCells: new Set(),
	w: false,
	ws: {},
}

const boostingCells = [];
const playerCells = [];
const players = new Set();
let nextCellId = 1;
let now = 0; // current tick
let pellets = 0;
let viruses = 0;

let statsBuffer = Buffer.from('{}\0');

const randomColors = new Uint32Array(1536);
for (let shade = 0; shade < 256; ++shade) {
	randomColors.set([
		0x10ff00 | shade, 0xff1000 | shade, // random red component
		0x1000ff | (shade << 8), 0xff0010 | (shade << 8), // random green component
		0x0010ff | (shade << 16), 0x00ff10 | (shade << 16), // random blue component
	], shade * 6);
}

const bounce = (cell, fromBoost) => {
	if (cell.x - cell.r < -settings.mapWidth) {
		cell.x = -settings.mapWidth + cell.r;
		if (fromBoost) cell.boostUnitX *= -1;
	} else if (settings.mapWidth < cell.x + cell.r) {
		cell.x = settings.mapWidth - cell.r;
		if (fromBoost) cell.boostUnitX *= -1;
	}
	if (cell.y - cell.r < -settings.mapWidth) {
		cell.y = -settings.mapWidth + cell.r;
		if (fromBoost) cell.boostUnitY *= -1;
	} else if (settings.mapWidth < cell.y + cell.r) {
		cell.y = settings.mapWidth - cell.r;
		if (fromBoost) cell.boostUnitY *= -1;
	}
};

const launch = (cell, radius, boostUnitX, boostUnitY, boostMagnitude) => {
	cell.r = Math.sqrt(cell.r * cell.r - radius * radius);
	const newCell = {
		type: CELL_TYPE_PLAYER,
		id: nextCellId++,
		x: cell.x + settings.playerSplitDistance * boostUnitX,
		y: cell.y + settings.playerSplitDistance * boostUnitY,
		r: radius,
		rgb: cell.rgb,
		born: now,
		changed: now,
		moved: now,
		dead: false,
		deadTo: 0,
		owner: cell.owner,
		boostUnitX,
		boostUnitY,
		boostMagnitude,
		encodingMove: EMPTY_BUFFER,
		encodingFirst: EMPTY_BUFFER,
	};
	encode(newCell);
	bitgridAdd(newCell);
	owner.owned.add(newCell);
	boostingCells.push(newCell);
	playerCells.push(newCell);
};

const remove = cell => {
	bitgridRemove(cell);
	if (cell.type === CELL_TYPE_PLAYER) {
		cell.owner.owned.delete(cell);
	} else if (cell.type === CELL_TYPE_PELLET) --pellets;
	else if (cell.type === CELL_TYPE_VIRUS) --viruses;
	// the cell will be removed from boostingCells and playerCells later
};

const CELL_EAT_SIZE_FACTOR = Math.sqrt(1.3); // cells must have 1.3x mass, so sqrt(1.3)x the radius
const leftEatsRight = (leftCell, rightCell) => {
	if (leftCell.type === CELL_TYPE_PLAYER) {
		// players eat everything, but minions only eat minions
		if (rightCell.type === CELL_TYPE_PLAYER && leftCell.owner.minion && !rightCell.owner.minion) return false;
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

	return leftCell.r * CELL_EAT_SIZE_FACTOR > rightCell.r;
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
	return leftCell.mergeable && rightCell.mergeable;
};

const safeSpawnPos = (radius) => {
	for (let i = 0; i < settings.worldSafeSpawnTries; ++i) {
		const x = (Math.random() * 2 - 1) * (settings.mapWidth - radius);
		const y = (Math.random() * 2 - 1) * (settings.mapHeight - radius);

		const xmin = ~~((x + settings.mapWidth - radius) / BITGRID_TILE_SIZE);
		const xmax = ~~((x + settings.mapWidth + radius) / BITGRID_TILE_SIZE);
		const ymin = ~~((y + settings.mapHeight - radius) / BITGRID_TILE_SIZE);
		const ymax = ~~((y + settings.mapHeight + radius) / BITGRID_TILE_SIZE);
		if (!bitgridSearch(xmin, xmax, ymin, ymax, cell => {
			if (cell.type === CELL_TYPE_PELLET) return;
			if (x - radius <= cell.x + cell.r && cell.x - cell.r <= x + radius
				&& y - radius <= cell.y + cell.r && cell.y - cell.r <= y + radius)
				return true;
		})) {
			return [x, y];
		}
	}

	const x = (Math.random() * 2 - 1) * (settings.mapWidth - radius);
	const y = (Math.random() * 2 - 1) * (settings.mapHeight - radius);
	return [x, y];
};

const encode = cell => {
	let move = cell.encodingMove;
	const moveByteLength = 14 + cell.owner.clan.byteLength;
	if (move.byteLength !== moveByteLength) cell.encodingMove = move = Buffer.alloc(moveByteLength);

	move.writeUInt32LE(cell.id, 0);
	move.writeInt16LE(cell.x, 4);
	move.writeInt16LE(cell.y, 6);
	move.writeInt16LE(cell.r, 8);

	let flags = 0;
	if (cell.type === CELL_TYPE_VIRUS) flags |= 1;
	if (cell.type === CELL_TYPE_EJECT) flags |= 0x20;
	move.writeUInt8(flags, 10);
	// move.writeUInt8(0, 11); // sigmally: isUpdate, this is never used
	// move.writeUInt8(0, 12); // sigmally: isPlayer, this is never used
	move.writeUInt8(cell.owner.sub ? 1 : 0, 13); // sigmally

	cell.owner.clan.copy(move, 14);

	let first = cell.encodingFirst;
	const firstByteLength = moveByteLength + 3 + cell.owner.name.byteLength + cell.owner.skin.byteLength;
	if (first.byteLength !== firstByteLength) cell.encodingFirst = first = Buffer.alloc(firstByteLength);
	move.copy(first);
	move.writeUInt8(flags | 0x02 | 0x04 | 0x08, 10); // add more flags (color, name, skin)

	let o = move.byteLength;
	move.writeUInt32LE(cell.rgb, o); // this will never overflow the bounds of `first`
	o += 3;
	cell.owner.name.copy(first, o);
	o += cell.owner.name.byteLength;
	cell.owner.skin.copy(first, o);

	cell.encodingMove = move;
	cell.encodingFirst = first;
};

const worldEatArray = [];
const worldRigidArray = [];
const worldTick = () => {
	const start = performance.now();

	// #1 update world

	// TODO: adjust cell ids if they get too high

	for (; pellets < settings.pelletCount; ++pellets) {
		const [x, y] = safeSpawnPos(settings.pelletMinSize); // TODO, this should probably not be safeSpawnPos
		const pellet = {
			type: CELL_TYPE_PELLET,
			id: nextCellId++,
			x,
			y,
			r: settings.pelletMinSize,
			rgb: randomColors[~~(Math.random() * 256 * 6)],
			born: now,
			moved: now,
			changed: now,
			dead: false,
			deadTo: 0,
			owner: PLAYER_OWNER_SERVER,
			boostUnitX: 0,
			boostUnitY: 0,
			boostMagnitude: 0,
			encodingMove: EMPTY_BUFFER,
			encodingFirst: EMPTY_BUFFER,
		};
		encode(pellet);
		bitgridAdd(pellet);
	}

	for (; viruses < settings.virusCount; ++viruses) {
		const [x, y] = safeSpawnPos(settings.virusSize);
		const virus = {
			type: CELL_TYPE_VIRUS,
			id: nextCellId++,
			x: Math.random() * (settings.mapWidth - settings.virusSize),
			y: Math.random() * (settings.mapHeight - settings.virusSize),
			r: settings.virusSize,
			rgb: 0x33ff33,
			born: now,
			moved: now,
			changed: now,
			dead: false,
			deadTo: 0,
			owner: PLAYER_OWNER_SERVER,
			boostUnitX: 0,
			boostUnitY: 0,
			boostMagnitude: 0,
			encodingMove: EMPTY_BUFFER,
			encodingFirst: EMPTY_BUFFER,
		};
		encode(virus);
		bitgridAdd(virus);
	}

	for (let i = 0, l = boostingCells.length; i < l; ++i) {
		const cell = boostingCells[i];
		cell.x += cell.boostUnitX * cell.boostMagnitude / 9;
		cell.y += cell.boostUnitY * cell.boostMagnitude / 9;
		cell.boostMagnitude -= 1;

		cell.moved = now;
		encode(cell);
		bitgridUpdate(cell);
	}
	let j = 0; // remove non-boosting cells all at once
	for (let i = 0, l = boostingCells.length; i < l; ++i) {
		boostingCells[j] = boostingCells[i];
		if (boostingCells[i].boostMagnitude > 0) ++j;
	}
	boostingCells.length = j;

	let eatL = 0;
	let rigidL = 0;
	const eat = worldEatArray;
	const rigid = worldRigidArray;
	eat.fill(); // set everything to undefined, but do not reduce the allocated size of the array
	rigid.fill();
	for (let i = 0, l = boostingCells.length; i < l; ++i) {
		const cell = boostingCells[i];
		if (cell.type === CELL_TYPE_PLAYER) continue;
		bitgridSearch(cell.xmin, cell.xmax, cell.ymin, cell.ymax, otherCell => {
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
			const d = Math.hypot(dx, dy);
			if (d >= 1) {
				// no idea where -0.4396754 comes from
				const realDistance = Math.min(d, 88 * (this.size ** -0.4396754)) * settings.playerMoveMult;
				cell.x += dx / d * realDistance;
				cell.y += dy / d * realDistance;
			}
		}

		cell.r -= cell.r * settings.playerDecayMult / 50;
		if (cell.r < settings.playerMinSize) cell.r = settings.playerMinSize;

		if (cell.r > settings.playerMaxSize) {
			const overflow = Math.ceil(cell.r * cell.r / (settings.playerMaxSize * settings.playerMaxSize));
			const splitCellCount = Math.min(overflow, settings.playerMaxCells - cell.owner.owned.size);
			const splitSize = Math.min(Math.sqrt(cell.r * cell.r / splitCellCount), settings.playerMaxSize);
			for (let i = 1; i < splitCellCount; ++i) {
				const angle = Math.random() * 2 * Math.PI;
				launch(cell, splitSize, Math.cos(angle), Math.sin(angle), settings.playerSplitBoost);
			}
			cell.r = splitSize;
		}

		bounce(cell);
		cell.moved = now;
		encode(cell);
		bitgridUpdate(cell);
	}

	for (let i = 0, l = playerCells.length; i < l; ++i) {
		const cell = playerCells[i];
		bitgridSearch(cell.xmin, cell.xmax, cell.ymin, cell.ymax, otherCell => {
			if (cell === otherCell) return;
			else if (leftCollidesRight(cell, otherCell)) rigid[rigidL++] = cell, rigid[rigidL++] = otherCell;
			else if (leftEatsRight(cell, otherCell)) eat[eatL++] = cell, eat[eatL++] = otherCell;
			else if (leftEatsRight(otherCell, cell)) eat[eatL++] = otherCell, eat[eatL++] = cell;
		});
	}

	for (let i = 0; i < rigidL; i += 2) {
		const a = rigid[i];
		const b = rigid[i + 1];

		const dx = b.x - a.x;
		const dy = b.y - a.y;
		const d = Math.hypot(dx, dy);
		const extraSpace = a.r + b.r - d;
		if (extraSpace <= 0) continue;
		if (d === 0) d = 1, dx = 1, dy = 0;

		const massA = a.r * a.r;
		const massB = b.r * b.r;
		const factorA = massA / (massA + massB);
		const factorB = massB / (massA + massB);
		a.x -= dx / d * extraSpace * factorA;
		a.y -= dy / d * extraSpace * factorA;
		b.x += dx / d * extraSpace * factorB;
		b.y += dy / d * extraSpace * factorB;

		bounce(a); bounce(b);
		a.moved = b.moved = now;
		encode(a); encode(b);
		bitgridUpdate(a); bitgridUpdate(b); // TODO maybe defer this if possible
	}

	for (let i = 0; i < eatL; i += 2) {
		const a = eat[i];
		const b = eat[i + 1];
		if (a.dead || b.dead) continue;

		const dx = b.x - a.x;
		const dy = b.y - a.y;
		const d = Math.hypot(dx, dy);
		if (d > a.r - b.r / settings.worldOverlapEatDiv) continue;

		a.r = Math.sqrt(a.r * a.r + b.r * b.r);
		a.moved = now;
		encode(a);
		bitgridUpdate(a);

		b.dead = true;
		b.deadTo = a.id;
		remove(b);
	}

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

	// now update players
	// find the largest player first
	let largestPlayer, largestPlayerMass = 0;
	for (const player of players) {
		let mass = 0;
		for (const cell of player.owned) {
			mass += cell.r * cell.r;
		}
		if (mass > largestPlayerMass) [largestPlayer, largestPlayerMass] = [player, mass];
	}

	for (const player of players) {
		if (player.disconnectedAt) {
			if (player.state === PLAYER_STATE_PLAYING && now - player.disconnectedAt > 25 * 60) {
				j = 0; // remove player's cells
				for (let i = 0, l = playerCells.length; i < l; ++i) {
					playerCells[j] = playerCells[i];
					if (playerCells[j].owner === player) ++j;
					else {
						playerCells[i].dead = true;
						bitgridRemove(playerCells[i]);
					}
				}
				playerCells.length = j;
				players.delete(player);
			} else if (player.state !== PLAYER_STATE_PLAYING) players.delete(player);
		} else {
			// split
			for (let i = 0; i < player.splits; ++i) {
				for (const cell of player.owned) {
					if (player.owned.size >= settings.playerMaxCells) break;
					if (cell.r < settings.playerMinSplitSize) continue;

					let dx = player.mouseX - cell.x;
					let dy = player.mouseY - cell.y;
					let d = Math.hypot(dx, dy);
					if (d < 1) d = 1, dx = 1, dy = 0;
					launch(cell, cell.r / settings.playerSplitSizeDiv, dx / d, dy / d, d);

					cell.r *= 1 - 1 / settings.playerSplitSizeDiv;
					cell.moved = now;
					encode(cell);
					bitgridUpdate(cell);
				}
			}
			player.splits = 0;

			// eject
			if (player.w) {
				for (const cell of player.owned) {
					if (cell.r < settings.playerMinEjectSize) continue;
					let dx = player.mouseX - cell.x;
					let dy = player.mouseY - cell.y;
					let d = Math.hypot(dx, dy);
					if (d < 1) d = 1, dx = 1, dy = 0;

					const angle = Math.atan2(dx, dy) + (Math.random() * 2 - 1) * settings.ejectDispersion;
					const eject = {
						type: CELL_TYPE_EJECT,
						id: nextCellId++,
						x: cell.x + cell.r * dx / d,
						y: cell.y + cell.r * dy / d,
						r: settings.ejectedSize,
						rgb: cell.rgb,
						born: now,
						moved: now,
						changed: now,
						dead: false,
						deadTo: 0,
						owner: PLAYER_OWNER_SERVER,
						boostUnitX: Math.cos(angle),
						boostUnitY: Math.sin(angle),
						boostMagnitude: settings.ejectedCellBoost,
						encodingMove: EMPTY_BUFFER,
						encodingFirst: EMPTY_BUFFER,
					};
					bitgridAdd(eject);
					encode(eject);
					boostingCells.push(eject);

					cell.r = Math.sqrt(cell.r * cell.r - eject.r * eject.r);
					encode(cell);
					bitgridUpdate(cell);
				}
			}

			// q press, and update state
			if (player.q) {
				if (player.state === PLAYER_STATE_ROAM) player.state = PLAYER_STATE_SPECTATE;
				else if (player.state === PLAYER_STATE_SPECTATE) player.state = PLAYER_STATE_ROAM;
			}
			if (player.state === PLAYER_STATE_SPECTATE && !largestPlayer) player.state = PLAYER_STATE_ROAM;

			// spawn request
			if (!player.owned.size) {
				if (!player.spawn && player.state === PLAYER_STATE_PLAYING) player.state = PLAYER_STATE_IDLE;
				else if (player.spawn) {
					// TODO: what if a player is in limbo?
					if (player.spawn.spectating) player.state = PLAYER_STATE_ROAM;
					else {
						const [x, y] = safeSpawnPos(settings.playerSpawnSize);
						const cell = {
							type: CELL_TYPE_PLAYER,
							id: nextCellId++,
							x: cell.x + settings.playerSplitDistance * boostUnitX,
							y: cell.y + settings.playerSplitDistance * boostUnitY,
							r: settings.playerSpawnSize,
							rgb: randomColors[~~(Math.random() * 256 * 6)],
							born: now,
							changed: now,
							moved: now,
							dead: false,
							deadTo: 0,
							owner: player,
							boostUnitX: 0,
							boostUnitY: 0,
							boostMagnitude: 0,
							encodingMove: EMPTY_BUFFER,
							encodingFirst: EMPTY_BUFFER,
						};
						player.owned.add(cell);
						bitgridAdd(cell);
						encode(cell);
						playerCells.push(cell);

						player.name = player.spawn.name;
						player.skin = player.spawn.skin;
						player.sub = player.spawn.sub;
						player.state = PLAYER_STATE_PLAYING;
					}
				}
			}
			if (player.spawn) player.spawn = undefined; // it should have been processed by now

			// update view area
			if (player.state === PLAYER_STATE_PLAYING) {
				let x = 0, y = 0, r = 0;
				for (const cell of player.owned) {
					x += cell.x;
					y += cell.y;
					r += cell.r;
				}
				player.camera = {
					x: x / player.owned.size,
					y: y / player.owned.size,
					scale: Math.min(64 / r, 1) ** 0.4,
				};
			} else if (player.state === PLAYER_STATE_ROAM) {
				const dx = player.mouseX - player.camera.x;
				const dy = player.mouseY - player.camera.y;
				const d = Math.hypot(dx, dy);
				const distance = Math.min(d, settings.playerRoamSpeed);
				if (distance >= 1) {
					player.camera = {
						x: Math.min(Math.max(player.camera.x + dx / d * distance, -settings.mapWidth), settings.mapWidth),
						y: Math.min(Math.max(player.camera.y + dy / d * distance, -settings.mapWidth), settings.mapWidth),
						scale: settings.playerRoamViewScale,
					};
				}
			} else if (player.state === PLAYER_STATE_SPECTATE) {
				player.camera = largestPlayer.camera;
			}
		}
	}

	// update stats, this will also be used for minions
	let playingExternal = 0;
	let playingInternal = 0;
	let spectating = 0;
	for (const player of players) {
		if (player.owner.minionCommander || player.owner.bot) ++playingInternal;
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
		if (!player.owner.minionCommander) continue;
		let minions = minionsPerPlayer.get(player.owner.minionCommander) || 0;
		if (minions > targetMinionsPerPlayer || player.owner.state !== PLAYER_STATE_PLAYING) {
			players.delete(player);
			player.disconnectedAt = -Infinity; // make sure its cells are immediately deleted
		} else {
			minionsPerPlayer.set(player.owner.minionCommander, minions + 1);
		}
	}

	// add new minions
	for (const player of players) {
		if (player.owner.minionCommander || player.owner.bot) continue;
		if (player.owner.state !== PLAYER_STATE_PLAYING) continue;
		let minions = minionsPerPlayer.get(player.owner.minionCommander) || 0;
		for (; minions < targetMinionsPerPlayer; ++minions) {
			players.add({
				bot: false,
				camera: { x: 0, y: 0, scale: 1 },
				clan: EMPTY_STRING,
				disconnectedAt: 0,
				minionCommander: player,
				mouseX: 0,
				mouseY: 0,
				name: EMPTY_STRING,
				owned: new Set(),
				q: false,
				showClanmates: false,
				skin: EMPTY_STRING,
				spawn: undefined,
				splits: 0,
				state: PLAYER_STATE_IDLE,
				sub: false,
				w: false,
			});
		}
	}

	// compile statistics
	const loadTime = performance.now() - start;
	statsBuffer = Buffer.from(JSON.stringify({
		limit: settings.listenerMaxConnections,
		internal: playingInternal, // might be outdated by one tick, but that's okay
		external: playingExternal + spectating,
		playing: playingExternal,
		spectating,
		name: settings.serverName,
		gamemode: 'FFA',
		loadTime: performance.now() - start,
		uptime: ~~(performance.now() - serverStartTime),
		// legacy
		mode: 'FFA',
		update: loadTime,
		playersTotal: playingExternal + spectating,
		playersAlive: playingExternal,
		playersSpect: spectating,
		playersLimit: settings.listenerMaxConnections,
	}));

	// #2 update connections
	for (const player of players) {
		if (player.disconnectedAt) continue;
		if (now - player.updated >= 60 * 25) {
			player.close();
			continue;
		}

		if (player.state === PLAYER_STATE_LIMBO) {
			// TODO enqueue into matchmaker if player.spawn
			player.spawn = undefined; // but make sure matchmaker enqueue is done first
			player.w = player.q = false;
			player.splits = 0;
			continue;
		}

		const visibleCells = new Set();
		const cameraWidth = 1920 / player.camera.scale / 2 * settings.playerViewScaleMult;
		const cameraHeight = 1080 / player.camera.scale / 2 * settings.playerViewScaleMult;
		const cameraXmin = player.camera.x - cameraWidth;
		const cameraXmax = player.camera.x + cameraWidth;
		const cameraYmin = player.camera.y - cameraHeight;
		const cameraYmax = player.camera.y + cameraHeight;
		const xmin = ~~(Math.max(cameraXmin + settings.mapWidth, 0) / BITGRID_TILE_SIZE);
		const xmax = ~~(Math.min(cameraXmax + settings.mapWidth, settings.mapWidth * 2) / BITGRID_TILE_SIZE);
		const ymin = ~~(Math.max(cameraYmin + settings.mapHeight, 0) / BITGRID_TILE_SIZE);
		const ymax = ~~(Math.min(cameraYmax + settings.mapHeight, settings.mapHeight * 2) / BITGRID_TILE_SIZE);
		bitgridSearch(xmin, xmax, ymin, ymax, cell => {
			if (cameraXmin <= cell.x + cell.r && cell.x - cell.r <= cameraXmax
				&& cameraYmin <= cell.y + cell.r && cell.y - cell.r <= cameraYmax) {
				visibleCells.add(cell);
			}
		});

		// the new Set.prototype.difference and .intersection functions are only faster if the two sets are very
		// disjoint, but usually they aren't (a player can't move that far between ticks)
		// also, they were only added in node.js 22, which is quite recent, so better to stick with the old method
		const oldVisibleCells = player.visibleCells;
		const newOwned = [];
		const eat = [];
		const add = [];
		const upd = [];
		const del = [];
		for (const cell of visibleCells) {
			if (oldVisibleCells.has(cell)) {
				if (cell.moved) upd.push(cell.encodingMove);
			} else {
				if (cell.owner === player) newOwned.push(cell.id);
				add.push(cell.encodingFirst);
			}
		}
		for (const cell of oldVisibleCells) {
			if (visibleCells.has(cell)) continue;
			if (cell.deadTo) eat.push(cell);
			else del.push(cell); // sigmally: non-sigmally clients require the cell to be in both eat and del
		}

		for (let i = 0; i < newOwned.length; ++i) {
			writer.writeUInt8(0x20, 0);
			writer.writeUInt32LE(newOwned[i], 1);
			player.ws.send(writer.slice(0, 5));
		}

		let o = 0;
		writer.writeUInt8(0x10, o++); // packet: update

		(writer.writeUInt16LE(eat.length, o), o += 2);
		for (let i = 0, l = eat.length; i < l; ++i) {
			(writer.writeUInt32LE(eat[i].id, o), o += 4);
			(writer.writeUInt32LE(eat[i].deadTo, o), o += 4);
		}

		for (let i = 0, l = add.length; i < l; ++i) {
			add[i].copy(writer, o);
			o += add[i].byteLength;
		}
		for (let i = 0, l = upd.length; i < l; ++i) {
			upd[i].copy(writer, o);
			o += upd[i].byteLength;
		}
		(writer.writeUInt32LE(0, o), o += 4);

		for (let i = 0, l = del.length; i < l; ++i) {
			(writer.writeUInt32LE(del[i].id, o), o += 4);
		}

		player.ws.send(writer.slice(0, o));
	}

	// #3 update matchmaker
	// #4 update gamemode-specific

	++now;
	setTimeout(worldTick, Math.max(performance.now() - start, 0));
};
worldTick();

//========== networking ================================================================================================

const SIG_VERSION_STRING = Buffer.from('SIG 0.0.1\0');
// SIG 0.0.1\0, then integers 0-255 (don't bother with opcode shuffling)
const SIG_HANDSHAKE = Buffer.alloc(SIG_VERSION_STRING.byteLength + 256);
SIG_VERSION_STRING.copy(SIG_HANDSHAKE);
for (let i = 0, o = SIG_VERSION_STRING.byteLength; i < 256; ++i, ++o) {
	SIG_HANDSHAKE.writeUInt8(i, o);
}

const BORDER_UPDATE_PACKET = Buffer.alloc(33);
BORDER_UPDATE_PACKET.writeUInt8(0x40, 0);
BORDER_UPDATE_PACKET.writeDoubleLE(-settings.mapWidth, 1);
BORDER_UPDATE_PACKET.writeDoubleLE(-settings.mapHeight, 9);
BORDER_UPDATE_PACKET.writeDoubleLE(settings.mapWidth, 17);
BORDER_UPDATE_PACKET.writeDoubleLE(settings.mapHeight, 25);

const wss = new WebSocketServer({ noPort: true }); // TODO noPort, then implement /server/recaptcha/v3 and all that
wss.on('connection', client => {
	let player;
	setTimeout(() => {
		if (!player && client.readyState <= 1) {
			client.close();
		}
	}, 5000);

	client.on('close', () => {
		if (!player) return;
		player.disconnectedAt = now;
	});
	client.on('error', () => {});
	client.on('message', buf => {
		// data must always be a Buffer, even though ws module is very ambiguous
		if (buf.byteLength >= 512 || !buf.byteLength) return client.close(1009, 'Unexpected message size');
		if (!player) {
			if (!data.equals(SIG_VERSION_STRING)) client.close(1003, 'Ambiguous protocol');

			player = {
				bot: false,
				camera: { x: 0, y: 0, scale: 1 },
				clan: EMPTY_STRING,
				disconnectedAt: 0,
				minionCommander: undefined,
				mouseX: 0,
				mouseY: 0,
				name: EMPTY_STRING,
				owned: new Set(),
				q: false,
				showClanmates: false,
				skin: EMPTY_STRING,
				spawn: undefined,
				splits: 0,
				state: PLAYER_STATE_IDLE,
				sub: false,
				updated: now,
				visibleCells: new Set(),
				w: false,
				ws: client,
			};
			players.add(player);

			client.send(SIG_HANDSHAKE);
			client.send(BORDER_UPDATE_PACKET);
			return;
		}

		player.updated = now;

		let o = 0;
		const readUtf8 = () => { // null-terminated utf8 string
			let start = o;
			while (o < buf.byteLength && !buf.readUInt8(o)) ++o;
			return buf.slice(start, o).toString('utf8');
		};
		const encodeUtf8 = s => {
			const base = s.toString('utf-8');
			const out = Buffer.alloc(base.byteLength + 1); // null-terminated
			for (let o = 0; o < base.byteLength; ++o) {
				out[o] = base[o] || 0xff; // get rid of null terminators
			}
			return out;
		};
		const opcode = buf.readUInt8(o++);
		if (opcode === 0) {
			let body;
			try {
				body = JSON.parse(readUtf8());
			} catch (_) {
				return client.close(1003, 'Unexpected message format');
			}

			if (typeof body !== 'object' || typeof body.name !== 'string') return client.close();
			if (body.skin && typeof body.skin !== 'string') return client.close();
			if (body.clan && typeof body.clan !== 'string') return client.close();

			const spectating = body.state ==/*=*/ 2;
			if (!spectating && settings.serverPassword && settings.serverPassword !== body.password) {
				client.send(Buffer.from([ 0xb4 ])); // password prompt
				return;
			}

			player.spawn = {
				name: encodeUtf8(body.name.substring(0, 64)),
				skin: encodeUtf8(body.skin.substring(0, 20)), // low limit, to prevent accessing things that aren't skins
				spectating,
				sub: !!body.sub,
			};
			player.clan = encodeUtf8(body.clan.substring(0, 32));
			player.showClanmates = !!body.showClanmates;
		} else if (opcode === 0x10) {
			if (buf.byteLength === 13) {
				player.mouseX = buf.readInt32LE(o);
				player.mouseY = buf.readInt32LE(o + 4);
			} else if (buf.byteLength === 9) { // no one actually uses this but it's supported
				player.mouseX = buf.readInt16LE(o);
				player.mouseY = buf.readInt16LE(o + 2);
			} else if (buf.byteLength === 21) {
				player.mouseX = ~~buf.readDoubleLE(o);
				player.mouseY = ~~buf.readDoubleLE(o + 8);
			} else client.close(1003, 'Unexpected message format');
		} else if (opcode === 0x17) ++player.splits;
		else if (opcode === 0x18) player.q = true;
		else if (opcode === 0x19) player.q = false;
		else if (opcode === 0x21) player.w = true;
		else if (opcode === 0x99) {
			if (buf.byteLength < 2) return client.close(1003, 'Bad message format');
			++o; // skip flags altogether
			const message = readUtf8();
			// TODO chat message, filtering and all that
		} else if (opcode === 0xfe) {
			// stats
			if (player.limbo) return;
			client.send(statsBuffer);
		}
	});
});
