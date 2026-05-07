const COLS = 10;
const ROWS = 20;
const CELL = 30;
const DAS_DELAY = 170;
const ARR_RATE = 30;
const NEXT_QUEUE_SIZE = 3;

const COLORS = {
  I: '#00cfcf', O: '#cfcf00', T: '#9f00cf',
  S: '#00cf00', Z: '#cf0000', J: '#0000cf', L: '#cf7f00',
  ghost: 'rgba(255,255,255,0.12)',
};

const PIECES = {
  I: [[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]],
  O: [[1,1],[1,1]],
  T: [[0,1,0],[1,1,1],[0,0,0]],
  S: [[0,1,1],[1,1,0],[0,0,0]],
  Z: [[1,1,0],[0,1,1],[0,0,0]],
  J: [[1,0,0],[1,1,1],[0,0,0]],
  L: [[0,0,1],[1,1,1],[0,0,0]],
};

const SCORES       = [0, 100, 300, 500, 800];
const TSPIN_SCORES = [400, 800, 1200, 1600];

const boardCanvas  = document.getElementById('board');
const overlayCanvas = document.getElementById('overlay');
const nextCanvas   = document.getElementById('next');
const holdCanvas   = document.getElementById('hold');
const bCtx = boardCanvas.getContext('2d');
const oCtx = overlayCanvas.getContext('2d');
const nCtx = nextCanvas.getContext('2d');
const hCtx = holdCanvas.getContext('2d');

let board, current, nextQueue, hold, holdUsed;
let score, level, lines, best;
let gameRunning, paused, gameOver;
let dropInterval, lastTime, dropCounter;
let bag, bagIndex;
let boardDirty, lastRotated;
let tspinLabel = '', tspinLabelTimer = null;

let dasDirection = null, dasTimer = null, arrTimer = null;

// ─── Audio ────────────────────────────────────────────────────

let audioCtx = null;

function getAudio() {
  if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  if (audioCtx.state === 'suspended') audioCtx.resume();
  return audioCtx;
}

function playTone(freq, duration, type = 'sine', vol = 0.25, delay = 0) {
  try {
    const ctx = getAudio();
    const t = ctx.currentTime + delay;
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.connect(gain);
    gain.connect(ctx.destination);
    osc.type = type;
    osc.frequency.setValueAtTime(freq, t);
    gain.gain.setValueAtTime(vol, t);
    gain.gain.exponentialRampToValueAtTime(0.001, t + duration);
    osc.start(t);
    osc.stop(t + duration + 0.02);
  } catch (_) {}
}

function sndMove()     { playTone(330, 0.04, 'sine', 0.07); }
function sndRotate()   { playTone(440, 0.05, 'sine', 0.09); }
function sndHold()     { playTone(330, 0.07, 'sine', 0.10); }
function sndLock()     { playTone(110, 0.09, 'sawtooth', 0.14); }
function sndHardDrop() {
  playTone(90, 0.10, 'sawtooth', 0.18);
  playTone(45, 0.08, 'sine', 0.12, 0.06);
}
function sndLineClear(count) {
  if (count === 4) {
    [262, 330, 392, 523, 659].forEach((f, i) => playTone(f, 0.14, 'square', 0.20, i * 0.07));
  } else {
    [330, 440, 523, 659].slice(0, count).forEach((f, i) => playTone(f, 0.12, 'sine', 0.20, i * 0.06));
  }
}
function sndTSpin() {
  playTone(587, 0.10, 'sine', 0.20);
  playTone(740, 0.10, 'sine', 0.22, 0.10);
  playTone(880, 0.15, 'sine', 0.28, 0.20);
}
function sndLevelUp() {
  [262, 330, 392, 523].forEach((f, i) => playTone(f, 0.10, 'square', 0.18, i * 0.06));
}
function sndGameOver() {
  [523, 440, 349, 262, 196].forEach((f, i) => playTone(f, 0.20, 'sine', 0.20, i * 0.14));
}

// ─── Bag / Piece ──────────────────────────────────────────────

function createBoard() {
  return Array.from({ length: ROWS }, () => Array(COLS).fill(null));
}

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function refillBag() { bag = shuffle(Object.keys(PIECES)); bagIndex = 0; }

function nextFromBag() {
  if (bagIndex >= bag.length) refillBag();
  return bag[bagIndex++];
}

function createPiece(type) {
  const matrix = PIECES[type].map(row => [...row]);
  return { type, matrix,
    x: Math.floor(COLS / 2) - Math.floor(matrix[0].length / 2), y: 0 };
}

// ─── Rotation ─────────────────────────────────────────────────

function rotate(m)    { return m[0].map((_, i) => m.map(r => r[i]).reverse()); }
function rotateCCW(m) { return m[0].map((_, i) => m.map(r => r[r.length - 1 - i])); }

// ─── Collision ────────────────────────────────────────────────

function collides(piece, dx = 0, dy = 0, mat = piece.matrix) {
  for (let r = 0; r < mat.length; r++) {
    for (let c = 0; c < mat[r].length; c++) {
      if (!mat[r][c]) continue;
      const nx = piece.x + c + dx, ny = piece.y + r + dy;
      if (nx < 0 || nx >= COLS || ny >= ROWS) return true;
      if (ny >= 0 && board[ny][nx]) return true;
    }
  }
  return false;
}

function wallKick(piece, rotated) {
  for (const dx of [0, -1, 1, -2, 2]) {
    if (!collides({ ...piece, matrix: rotated }, dx)) return dx;
  }
  return null;
}

// ─── T-Spin ───────────────────────────────────────────────────

function checkTSpin() {
  if (current.type !== 'T' || !lastRotated) return false;
  let filled = 0;
  for (const [dr, dc] of [[0,0],[0,2],[2,0],[2,2]]) {
    const r = current.y + dr, c = current.x + dc;
    if (c < 0 || c >= COLS || r >= ROWS || (r >= 0 && board[r][c])) filled++;
  }
  return filled >= 3;
}

function showTSpinLabel(label) {
  tspinLabel = label;
  clearTimeout(tspinLabelTimer);
  tspinLabelTimer = setTimeout(() => { tspinLabel = ''; }, 1200);
}

// ─── Game Logic ───────────────────────────────────────────────

function lock() {
  const isTSpin = checkTSpin();
  for (let r = 0; r < current.matrix.length; r++) {
    for (let c = 0; c < current.matrix[r].length; c++) {
      if (!current.matrix[r][c]) continue;
      const row = current.y + r;
      if (row < 0) { endGame(); return; }
      board[row][current.x + c] = current.type;
    }
  }
  boardDirty = true;
  const linesCleared = clearLines(isTSpin);
  if (!isTSpin && linesCleared === 0) sndLock();
  spawnPiece();
}

function clearLines(isTSpin = false) {
  let cleared = 0;
  for (let r = ROWS - 1; r >= 0; r--) {
    if (board[r].every(cell => cell)) {
      board.splice(r, 1);
      board.unshift(Array(COLS).fill(null));
      cleared++;
      r++;
    }
  }

  if (isTSpin) {
    score += TSPIN_SCORES[cleared] * level;
    showTSpinLabel(cleared === 0 ? 'T-SPIN' : `T-SPIN\n${['','싱글','더블','트리플'][cleared]}`);
    sndTSpin();
    if (cleared > 0) sndLineClear(cleared);
  } else if (cleared > 0) {
    score += SCORES[cleared] * level;
    sndLineClear(cleared);
  }

  if (cleared > 0) {
    lines += cleared;
    const prevLevel = level;
    level = Math.floor(lines / 10) + 1;
    dropInterval = Math.max(100, 1000 - (level - 1) * 90);
    if (level > prevLevel) sndLevelUp();
  }
  updateStats();
  return cleared;
}

function spawnPiece() {
  holdUsed = false;
  lastRotated = false;
  current = createPiece(nextQueue.shift().type);
  nextQueue.push(createPiece(nextFromBag()));
  if (collides(current)) { endGame(); return; }
  drawNext();
}

function holdPiece() {
  if (holdUsed) return;
  holdUsed = true;
  lastRotated = false;
  sndHold();
  if (!hold) {
    hold = createPiece(current.type);
    spawnPiece();
  } else {
    const tmp = hold;
    hold = createPiece(current.type);
    current = createPiece(tmp.type);
  }
  drawHold();
}

function ghostRow() {
  let dy = 0;
  while (!collides(current, 0, dy + 1)) dy++;
  return current.y + dy;
}

function hardDrop() {
  let dy = 0;
  while (!collides(current, 0, dy + 1)) dy++;
  score += dy * 2;
  current.y += dy;
  lastRotated = false;
  sndHardDrop();
  updateStats();
  lock();
}

function moveLeft()  { if (!collides(current, -1)) { current.x--; lastRotated = false; sndMove(); } }
function moveRight() { if (!collides(current,  1)) { current.x++; lastRotated = false; sndMove(); } }

function moveDown() {
  if (!collides(current, 0, 1)) {
    current.y++;
    score += 1;
    updateStats();
    dropCounter = 0;
  } else {
    lock();
  }
}

function rotatePiece(ccw = false) {
  const rotated = ccw ? rotateCCW(current.matrix) : rotate(current.matrix);
  const kick = wallKick(current, rotated);
  if (kick !== null) {
    current.matrix = rotated;
    current.x += kick;
    lastRotated = true;
    sndRotate();
  }
}

// ─── DAS ──────────────────────────────────────────────────────

function startDAS(dir) {
  if (dasDirection === dir) return;
  stopDAS();
  dasDirection = dir;
  if (dir === 'left') moveLeft(); else moveRight();
  dasTimer = setTimeout(() => {
    arrTimer = setInterval(() => {
      if (!gameRunning || paused || gameOver) { stopDAS(); return; }
      if (dir === 'left') moveLeft(); else moveRight();
    }, ARR_RATE);
  }, DAS_DELAY);
}

function stopDAS(dir) {
  if (dir && dasDirection !== dir) return;
  dasDirection = null;
  clearTimeout(dasTimer);
  clearInterval(arrTimer);
  dasTimer = arrTimer = null;
}

// ─── Touch ────────────────────────────────────────────────────

let touchStartX = 0, touchStartY = 0, touchStartTime = 0;
let softDropInterval = null;

function startSoftDrop() {
  if (softDropInterval) return;
  moveDown();
  softDropInterval = setInterval(() => {
    if (!gameRunning || paused || gameOver) { stopSoftDrop(); return; }
    moveDown();
  }, 80);
}

function stopSoftDrop() {
  clearInterval(softDropInterval);
  softDropInterval = null;
}

overlayCanvas.addEventListener('touchstart', (e) => {
  e.preventDefault();
  const t = e.touches[0];
  touchStartX = t.clientX;
  touchStartY = t.clientY;
  touchStartTime = Date.now();
}, { passive: false });

overlayCanvas.addEventListener('touchend', (e) => {
  e.preventDefault();
  if (!gameRunning || paused || gameOver) return;
  const dx = e.changedTouches[0].clientX - touchStartX;
  const dy = e.changedTouches[0].clientY - touchStartY;
  const dt = Date.now() - touchStartTime;
  const dist = Math.sqrt(dx * dx + dy * dy);

  if (dist < 20 && dt < 250) {
    rotatePiece(false);
    return;
  }
  if (Math.abs(dx) > Math.abs(dy)) {
    if (dx < -30) moveLeft();
    else if (dx > 30) moveRight();
  } else {
    if (dy > 30) hardDrop();
    else if (dy < -30) holdPiece();
  }
}, { passive: false });

function setupTouchBtn(id, onDown, onUp = null) {
  const el = document.getElementById(id);
  if (!el) return;
  el.addEventListener('pointerdown', (e) => {
    e.preventDefault();
    getAudio();
    if (gameRunning && !paused && !gameOver) onDown();
  });
  if (onUp) {
    el.addEventListener('pointerup', onUp);
    el.addEventListener('pointerleave', onUp);
    el.addEventListener('pointercancel', onUp);
  }
}

function initTouchButtons() {
  setupTouchBtn('btnLeft',
    () => startDAS('left'),
    () => stopDAS('left'));
  setupTouchBtn('btnRight',
    () => startDAS('right'),
    () => stopDAS('right'));
  setupTouchBtn('btnDown',
    () => startSoftDrop(),
    () => stopSoftDrop());
  setupTouchBtn('btnRotateCCW', () => rotatePiece(true));
  setupTouchBtn('btnRotateCW',  () => rotatePiece(false));
  setupTouchBtn('btnHardDrop',  () => hardDrop());
  setupTouchBtn('btnHold',      () => holdPiece());
}

// ─── Drawing ──────────────────────────────────────────────────

function drawCell(ctx, x, y, color, size = CELL) {
  ctx.fillStyle = color;
  ctx.fillRect(x * size + 1, y * size + 1, size - 2, size - 2);
  ctx.fillStyle = 'rgba(255,255,255,0.15)';
  ctx.fillRect(x * size + 1, y * size + 1, size - 2, 4);
  ctx.fillStyle = 'rgba(0,0,0,0.2)';
  ctx.fillRect(x * size + 1, y * size + size - 5, size - 2, 4);
}

function drawGrid(ctx) {
  ctx.strokeStyle = 'rgba(255,255,255,0.04)';
  ctx.lineWidth = 0.5;
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      ctx.strokeRect(c * CELL, r * CELL, CELL, CELL);
}

function drawBoard() {
  bCtx.clearRect(0, 0, boardCanvas.width, boardCanvas.height);
  drawGrid(bCtx);
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (board[r][c]) drawCell(bCtx, c, r, COLORS[board[r][c]]);
}

function drawOverlay() {
  oCtx.clearRect(0, 0, overlayCanvas.width, overlayCanvas.height);
  if (!current || !gameRunning || gameOver) return;

  const gy = ghostRow();
  if (gy !== current.y) {
    for (let r = 0; r < current.matrix.length; r++)
      for (let c = 0; c < current.matrix[r].length; c++) {
        if (!current.matrix[r][c]) continue;
        drawCell(oCtx, current.x + c, gy + r, COLORS.ghost);
      }
  }

  for (let r = 0; r < current.matrix.length; r++)
    for (let c = 0; c < current.matrix[r].length; c++) {
      if (!current.matrix[r][c]) continue;
      drawCell(oCtx, current.x + c, current.y + r, COLORS[current.type]);
    }

  if (tspinLabel) {
    oCtx.save();
    oCtx.font = 'bold 20px Courier New';
    oCtx.textAlign = 'center';
    oCtx.fillStyle = '#cc88ff';
    oCtx.shadowColor = '#9f00cf';
    oCtx.shadowBlur = 10;
    tspinLabel.split('\n').forEach((ln, i) =>
      oCtx.fillText(ln, overlayCanvas.width / 2, 60 + i * 26));
    oCtx.restore();
  }

  if (paused) {
    oCtx.fillStyle = 'rgba(0,0,0,0.6)';
    oCtx.fillRect(0, 0, overlayCanvas.width, overlayCanvas.height);
    oCtx.fillStyle = '#fff';
    oCtx.font = 'bold 28px Courier New';
    oCtx.textAlign = 'center';
    oCtx.fillText('PAUSED', overlayCanvas.width / 2, overlayCanvas.height / 2);
  }
}

function drawNext() {
  nCtx.clearRect(0, 0, nextCanvas.width, nextCanvas.height);
  nextQueue.forEach((piece, idx) => {
    const size = idx === 0 ? 22 : 16;
    const slotH = idx === 0 ? 110 : 85;
    const slotY = idx === 0 ? 0 : 110 + (idx - 1) * 85;
    const cols = piece.matrix[0].length, rows = piece.matrix.length;
    const ox = Math.floor((nextCanvas.width - cols * size) / 2);
    const oy = slotY + Math.floor((slotH - rows * size) / 2);
    for (let r = 0; r < rows; r++)
      for (let c = 0; c < cols; c++) {
        if (!piece.matrix[r][c]) continue;
        nCtx.fillStyle = COLORS[piece.type];
        nCtx.fillRect(ox + c * size + 1, oy + r * size + 1, size - 2, size - 2);
        nCtx.fillStyle = 'rgba(255,255,255,0.15)';
        nCtx.fillRect(ox + c * size + 1, oy + r * size + 1, size - 2, 4);
      }
    if (idx < NEXT_QUEUE_SIZE - 1) {
      nCtx.strokeStyle = 'rgba(255,255,255,0.08)';
      nCtx.lineWidth = 1;
      nCtx.beginPath();
      nCtx.moveTo(8, slotY + slotH);
      nCtx.lineTo(nextCanvas.width - 8, slotY + slotH);
      nCtx.stroke();
    }
  });
}

function drawPreview(ctx, piece, sz = 120) {
  ctx.clearRect(0, 0, sz, sz);
  if (!piece) return;
  const s = 24;
  const cols = piece.matrix[0].length, rows = piece.matrix.length;
  const ox = Math.floor((sz - cols * s) / 2);
  const oy = Math.floor((sz - rows * s) / 2);
  for (let r = 0; r < rows; r++)
    for (let c = 0; c < cols; c++) {
      if (!piece.matrix[r][c]) continue;
      ctx.fillStyle = COLORS[piece.type];
      ctx.fillRect(ox + c * s + 1, oy + r * s + 1, s - 2, s - 2);
      ctx.fillStyle = 'rgba(255,255,255,0.15)';
      ctx.fillRect(ox + c * s + 1, oy + r * s + 1, s - 2, 4);
    }
}

function drawHold() { drawPreview(hCtx, hold); }

function updateStats() {
  document.getElementById('score').textContent = score.toLocaleString();
  document.getElementById('level').textContent = level;
  document.getElementById('lines').textContent = lines;
  document.getElementById('best').textContent = best.toLocaleString();
}

function showGameOver() {
  const isNewBest = score > 0 && score >= best;
  const cx = overlayCanvas.width / 2, cy = overlayCanvas.height / 2;
  oCtx.fillStyle = 'rgba(0,0,0,0.78)';
  oCtx.fillRect(0, 0, overlayCanvas.width, overlayCanvas.height);
  oCtx.font = 'bold 30px Courier New';
  oCtx.textAlign = 'center';
  oCtx.fillStyle = '#ff4444';
  oCtx.fillText('GAME OVER', cx, cy - 80);
  if (isNewBest) {
    oCtx.fillStyle = '#ffdd00';
    oCtx.font = 'bold 16px Courier New';
    oCtx.fillText('★ NEW BEST! ★', cx, cy - 48);
  }
  [['SCORE','LEVEL'], ['LINES','BEST']].forEach(([l1, l2], row) => {
    oCtx.font = '14px Courier New';
    oCtx.fillStyle = '#888';
    oCtx.fillText(l1, cx - 60, cy - 10 + row * 56);
    oCtx.fillText(l2, cx + 60, cy - 10 + row * 56);
    oCtx.fillStyle = row === 1 && isNewBest ? '#ffdd00' : '#fff';
    oCtx.font = 'bold 20px Courier New';
    oCtx.fillStyle = '#fff';
    oCtx.fillText(row === 0 ? score.toLocaleString() : lines, cx - 60, cy + 16 + row * 56);
    oCtx.fillStyle = row === 1 && isNewBest ? '#ffdd00' : '#fff';
    oCtx.fillText(row === 0 ? level : best.toLocaleString(), cx + 60, cy + 16 + row * 56);
  });
  oCtx.fillStyle = '#666';
  oCtx.font = '13px Courier New';
  oCtx.fillText('시작 버튼을 눌러 재시작', cx, cy + 110);
  document.getElementById('startBtn').textContent = '재시작';
}

function endGame() {
  gameOver = true;
  gameRunning = false;
  stopDAS();
  stopSoftDrop();
  if (score > best) {
    best = score;
    localStorage.setItem('tetrisBest', best);
  }
  sndGameOver();
  showGameOver();
}

// ─── Init & Loop ──────────────────────────────────────────────

function initGame() {
  board = createBoard();
  score = 0; level = 1; lines = 0;
  hold = null; holdUsed = false;
  dropInterval = 1000; dropCounter = 0; lastTime = 0;
  gameRunning = true; paused = false; gameOver = false;
  boardDirty = true; lastRotated = false;
  tspinLabel = '';
  stopDAS();
  stopSoftDrop();
  best = parseInt(localStorage.getItem('tetrisBest') || '0', 10);
  refillBag();
  nextQueue = Array.from({ length: NEXT_QUEUE_SIZE }, () => createPiece(nextFromBag()));
  spawnPiece();
  updateStats();
  drawHold();
  document.getElementById('startBtn').textContent = '재시작';
}

function gameLoop(timestamp) {
  if (!gameRunning) return;
  const delta = timestamp - lastTime;
  lastTime = timestamp;
  if (!paused) {
    dropCounter += delta;
    if (dropCounter >= dropInterval) {
      dropCounter = 0;
      if (!collides(current, 0, 1)) current.y++;
      else lock();
    }
    if (boardDirty) { drawBoard(); boardDirty = false; }
    drawOverlay();
  }
  requestAnimationFrame(gameLoop);
}

// ─── Keyboard ─────────────────────────────────────────────────

document.getElementById('startBtn').addEventListener('click', () => {
  getAudio();
  initGame();
  requestAnimationFrame(gameLoop);
});

document.addEventListener('keydown', (e) => {
  if (!gameRunning || gameOver) return;
  if (paused && e.code !== 'KeyP') return;
  switch (e.code) {
    case 'ArrowLeft':  startDAS('left');     e.preventDefault(); break;
    case 'ArrowRight': startDAS('right');    e.preventDefault(); break;
    case 'ArrowDown':  moveDown();           e.preventDefault(); break;
    case 'ArrowUp': case 'KeyX': rotatePiece(false); e.preventDefault(); break;
    case 'KeyZ':   rotatePiece(true);        e.preventDefault(); break;
    case 'Space':  hardDrop();               e.preventDefault(); break;
    case 'KeyC':   holdPiece();              break;
    case 'KeyP':
      paused = !paused;
      if (!paused) { lastTime = performance.now(); requestAnimationFrame(gameLoop); }
      break;
  }
});

document.addEventListener('keyup', (e) => {
  if (e.code === 'ArrowLeft')  stopDAS('left');
  if (e.code === 'ArrowRight') stopDAS('right');
});

// ─── Boot ─────────────────────────────────────────────────────

initTouchButtons();

best = parseInt(localStorage.getItem('tetrisBest') || '0', 10);
document.getElementById('best').textContent = best.toLocaleString();
bCtx.fillStyle = '#111122';
bCtx.fillRect(0, 0, boardCanvas.width, boardCanvas.height);
drawGrid(bCtx);
oCtx.fillStyle = 'rgba(0,0,0,0.5)';
oCtx.fillRect(0, 0, overlayCanvas.width, overlayCanvas.height);
oCtx.fillStyle = '#aaaaff';
oCtx.font = 'bold 32px Courier New';
oCtx.textAlign = 'center';
oCtx.fillText('TETRIS', overlayCanvas.width / 2, overlayCanvas.height / 2 - 20);
oCtx.fillStyle = '#888';
oCtx.font = '16px Courier New';
oCtx.fillText('시작 버튼을 누르세요', overlayCanvas.width / 2, overlayCanvas.height / 2 + 20);
