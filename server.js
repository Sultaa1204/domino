// سيرفر ضومنة أونلاين — بدون أي مكتبات خارجية (Node 18 أو أحدث)
// السيرفر هو اللي يوزّع الأحجار ويتحكم باللعب، وكل لاعب ما يوصله إلا أحجاره.
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const crypto = require('crypto');
const { performance } = require('perf_hooks');

const PORT = process.env.PORT || 3000;
const PUB = path.join(__dirname, 'public');
const BOT_THINK_MS = +process.env.BOT_THINK_MS || 350;   // وقت تفكير اللاعب الآلي
const AWAY_BOT_MS = +process.env.AWAY_BOT_MS || 25000;                                // لو لاعب فصل، الآلي يلعب عنه بعد هالوقت
const TARGET = 101;

/* ---------- المحرك ---------- */
const ctx = { console, Math, performance, setTimeout };
vm.createContext(ctx);
vm.runInContext(fs.readFileSync(path.join(__dirname, 'engine.js'), 'utf8'), ctx);
const E = ctx.E;

/* ---------- الغرف ---------- */
const rooms = new Map();
const newCode = () => {
  let c;
  do { c = String(Math.floor(1000 + Math.random() * 9000)); } while (rooms.has(c));
  return c;
};
const newToken = () => crypto.randomBytes(12).toString('hex');
const cleanName = n => String(n || '').replace(/[<>]/g, '').trim().slice(0, 16) || 'لاعب';
const BOT_NAMES = ['بوت نمر', 'بوت صقر', 'بوت ذيب'];

function createRoom(n, name) {
  const code = newCode();
  const token = newToken();
  const room = {
    code, n, state: 'lobby', host: token, touched: Date.now(),
    seats: Array.from({ length: n }, () => ({ type: 'empty', name: '', token: null })),
    players: new Map(),          // token -> {name, seat}
    streams: new Map(),          // token -> Set(res)
    score: [0, 0], round: 0, starter: null, events: [], seq: 0,
    game: null, result: null, timer: null
  };
  rooms.set(code, room);
  room.players.set(token, { name: cleanName(name), seat: null });
  takeSeat(room, token, 0);
  return { room, token };
}

function takeSeat(room, token, seat) {
  const p = room.players.get(token);
  if (!p || room.state !== 'lobby') return false;
  if (seat < 0 || seat >= room.n || room.seats[seat].type === 'human') return false;
  if (p.seat !== null) room.seats[p.seat] = { type: 'empty', name: '', token: null };
  room.seats[seat] = { type: 'human', name: p.name, token };
  p.seat = seat;
  return true;
}

function joinRoom(room, name, token) {
  if (token && room.players.has(token)) return token;          // رجوع لنفس المقعد
  const t = newToken();
  room.players.set(t, { name: cleanName(name), seat: null });
  if (room.state === 'lobby') {
    const order = room.n === 4 ? [2, 1, 3] : [1];
    const free = order.find(s => room.seats[s].type === 'empty');
    if (free !== undefined) takeSeat(room, t, free);
  }
  return t;
}

const connected = (room, token) => !!(token && room.streams.get(token) && room.streams.get(token).size);

/* ---------- وش يشوف كل لاعب ---------- */
function viewFor(room, token) {
  const me = room.players.get(token);
  const mySeat = me ? me.seat : null;
  const v = {
    code: room.code, n: room.n, state: room.state, mySeat,
    isHost: token === room.host, myName: me ? me.name : '',
    seats: room.seats.map(s => ({ type: s.type, name: s.name, online: s.type === 'human' ? connected(room, s.token) : true, host: s.token === room.host })),
    score: room.score, target: TARGET, round: room.round, seq: room.seq,
    events: room.events.slice(-40)
  };
  const g = room.game;
  if (g) {
    v.game = {
      roundId: g.roundId, moveNo: g.moveNo, turn: g.turn,
      board: g.board.map(t => ({ t: [t[0], t[1]], by: t.by })),
      counts: g.hands.map(h => h.length),
      myHand: mySeat !== null ? g.hands[mySeat].map(t => [t[0], t[1]]) : [],
      boneCount: g.bone.length,
      slots: g.slots,
      forcedFirst: g.forcedFirst,
      passed: g.passed, drawCount: g.drawCount,
      lastMove: g.lastMove
    };
  }
  if (room.result) v.result = room.result;
  return v;
}

function send(res, v) { res.write(`data: ${JSON.stringify(v)}\n\n`); }
function broadcast(room) {
  room.touched = Date.now();
  for (const [token, set] of room.streams) {
    const v = viewFor(room, token);
    for (const res of set) send(res, v);
  }
}
function pushEvent(room, e) {
  room.seq++;
  room.events.push({ ...e, seq: room.seq });
  if (room.events.length > 80) room.events.shift();
}

/* ---------- منطق اللعب ---------- */
function startMatch(room) {
  room.score = [0, 0];
  room.round = 0;
  room.starter = null;
  room.seats.forEach((s, i) => {
    if (s.type === 'empty') room.seats[i] = { type: 'bot', name: BOT_NAMES[i % 3], token: null };
  });
  startRound(room);
}

function startRound(room) {
  const N = room.n;
  const deck = E.shuffle(E.fullSet());
  const g = {
    n: N, roundId: newToken().slice(0, 8), runId: Math.random(),
    hands: Array.from({ length: N }, (_, q) => deck.slice(q * 7, (q + 1) * 7)),
    bone: deck.slice(N * 7), board: [],
    slots: Array.from({ length: N }, () => [0, 0, 0, 0, 0, 0, 0]),
    forcedFirst: null, passes: 0, moveNo: 0, lastMove: null,
    passed: Array(N).fill(false), drawCount: Array(N).fill(0)
  };
  room.round++;
  room.result = null;
  room.events = [];
  if (room.starter === null) {
    let best = null, who = 0;
    for (let p = 0; p < N; p++) for (const t of g.hands[p]) {
      const val = E.isDouble(t) ? 100 + t[0] : E.pips(t);
      if (!best || val > best.v) { best = { v: val, t }; who = p; }
    }
    g.turn = who;
    g.forcedFirst = best.t;
    pushEvent(room, { type: 'start', seat: who, tile: [best.t[0], best.t[1]] });
  } else {
    g.turn = room.starter;
    pushEvent(room, { type: 'start', seat: g.turn });
  }
  room.game = g;
  room.state = 'playing';
  broadcast(room);
  schedule(room);
}

function schedule(room) {
  clearTimeout(room.timer);
  if (room.state !== 'playing') return;
  const g = room.game, p = g.turn, seat = room.seats[p];
  const moves = E.legalMoves(g.hands[p], g.board, g.forcedFirst);
  if (!moves.length) {
    room.timer = setTimeout(() => autoDrawPass(room, p), 900);
  } else if (seat.type === 'bot') {
    room.timer = setTimeout(() => botMove(room, p), 700);
  } else if (!connected(room, seat.token)) {
    room.timer = setTimeout(() => botMove(room, p), AWAY_BOT_MS);
  }
  // لاعب متصل: ننتظر حركته
}

function autoDrawPass(room, p) {
  const g = room.game;
  if (room.state !== 'playing' || g.turn !== p) return;
  E.__setG(g);
  const e = E.ends(g.board);
  let drew = 0;
  while (!E.legalMoves(g.hands[p], g.board, null).length && g.bone.length) {
    g.hands[p].push(g.bone.pop());
    drew++;
  }
  const playable = E.legalMoves(g.hands[p], g.board, null).length > 0;
  if (e) E.knowDraw(p, e, drew, playable);
  const endsTxt = e ? E.uniq(e) : [];
  if (drew) { g.drawCount[p] = drew; pushEvent(room, { type: 'draw', seat: p, n: drew, ends: endsTxt }); }
  if (!playable) {
    pushEvent(room, { type: 'pass', seat: p, ends: endsTxt });
    applyMove(room, p, null);
    return;
  }
  broadcast(room);
  schedule(room);
}

function botMove(room, p) {
  const g = room.game;
  if (room.state !== 'playing' || g.turn !== p) return;
  E.__setG(g);
  const moves = E.legalMoves(g.hands[p], g.board, g.forcedFirst);
  if (!moves.length) return autoDrawPass(room, p);
  let best = moves[0];
  if (moves.length > 1) {
    const job = E.newJob(p, 1500);
    E.jobStep(job, BOT_THINK_MS);
    best = E.jobResults(job)[0].m;
  }
  applyMove(room, p, best);
}

function applyMove(room, p, move) {
  const g = room.game;
  E.__setG(g);
  if (move) {
    let door = null;
    const e = E.ends(g.board);
    if (e && e[0] !== e[1]) door = move.side === 'L' ? e[0] : e[1];
    g.hands[p] = g.hands[p].filter(x => x !== move.t);
    g.board = E.place(g.board, move.t, move.side);
    const placed = move.side === 'L' ? g.board[0] : g.board[g.board.length - 1];
    placed.by = p;
    g.lastMove = { p, k: E.key(move.t) };
    g.forcedFirst = null;
    g.passes = 0;
    E.knowPlay(p, move.t);
    g.moveNo++;
    g.drawCount[p] = 0;
    g.passed[p] = false;
    pushEvent(room, { type: 'play', seat: p, tile: [move.t[0], move.t[1]], door });
    if (!g.hands[p].length) return endRound(room, p, 'domino');
  } else {
    g.passed[p] = true;
    g.passes++;
    if (g.passes >= g.n) return endRound(room, null, 'locked');
  }
  g.turn = (p + 1) % g.n;
  broadcast(room);
  schedule(room);
}

function endRound(room, seat, why) {
  const g = room.game;
  clearTimeout(room.timer);
  const sums = g.hands.map(h => E.sum(h.map(E.pips)));
  const ts = [0, 0];
  sums.forEach((x, q) => { ts[q % 2] += x; });
  let team;
  if (why === 'domino') team = seat % 2;
  else team = ts[0] < ts[1] ? 0 : ts[1] < ts[0] ? 1 : null;
  let pts = 0;
  if (team !== null) {
    pts = ts[1 - team];
    room.score[team] += pts;
    if (why === 'domino') room.starter = seat;
    else room.starter = sums.map((x, q) => [x, q]).filter(([, q]) => q % 2 === team).sort((a, b) => a[0] - b[0])[0][1];
  }
  const matchOver = room.score.some(x => x >= TARGET);
  room.result = {
    roundId: g.roundId, seat, team, why, sums, ts, pts, matchOver,
    hands: g.hands.map(h => h.map(t => [t[0], t[1]]))
  };
  room.state = matchOver ? 'matchEnd' : 'roundEnd';
  broadcast(room);
}

/* ---------- HTTP ---------- */
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.png': 'image/png', '.svg': 'image/svg+xml', '.ico': 'image/x-icon', '.json': 'application/json' };

function readBody(req) {
  return new Promise(resolve => {
    let data = '';
    req.on('data', c => { data += c; if (data.length > 10000) req.destroy(); });
    req.on('end', () => { try { resolve(JSON.parse(data || '{}')); } catch (_) { resolve({}); } });
  });
}
function json(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}

const api = {
  async create(b) {
    const n = b.n === 2 ? 2 : 4;
    const { room, token } = createRoom(n, b.name);
    return [200, { code: room.code, token }];
  },
  async join(b) {
    const room = rooms.get(String(b.code || ''));
    if (!room) return [404, { error: 'الغرفة مو موجودة. تأكد من الرقم.' }];
    const token = joinRoom(room, b.name, b.token);
    broadcast(room);
    return [200, { code: room.code, token }];
  },
  async seat(b, room, token) {
    if (!takeSeat(room, token, +b.seat)) return [400, { error: 'ما تقدر تجلس في هالمكان.' }];
    broadcast(room);
    return [200, { ok: true }];
  },
  async start(b, room, token) {
    if (token !== room.host) return [403, { error: 'المضيف بس يقدر يبدأ.' }];
    if (room.state !== 'lobby') return [400, { error: 'اللعب بادي.' }];
    startMatch(room);
    return [200, { ok: true }];
  },
  async play(b, room, token) {
    const p = room.players.get(token);
    const g = room.game;
    if (!g || room.state !== 'playing' || !p || p.seat !== g.turn) return [400, { error: 'مو دورك.' }];
    const moves = E.legalMoves(g.hands[p.seat], g.board, g.forcedFirst);
    const m = moves.find(x => E.key(x.t) === b.key && x.side === b.side)
      || (E.ends(g.board) && E.ends(g.board)[0] === E.ends(g.board)[1] && moves.find(x => E.key(x.t) === b.key));
    if (!m) return [400, { error: 'الحجر ما يركب هنا.' }];
    if (b.side === 'R' && m.side === 'L') m.side = 'R';
    applyMove(room, p.seat, m);
    return [200, { ok: true }];
  },
  async next(b, room) {
    if (room.state === 'roundEnd') startRound(room);
    else if (room.state === 'matchEnd') startMatch(room);
    return [200, { ok: true }];
  },
  async leave(b, room, token) {
    const p = room.players.get(token);
    if (p && p.seat !== null) {
      if (room.state === 'lobby') room.seats[p.seat] = { type: 'empty', name: '', token: null };
      else room.seats[p.seat] = { type: 'bot', name: `بوت بدل ${p.name}`, token: null };
    }
    room.players.delete(token);
    if (token === room.host) {
      const next = [...room.players.entries()].find(([, x]) => x.seat !== null);
      room.host = next ? next[0] : null;
    }
    const humans = room.seats.filter(s => s.type === 'human').length;
    if (!humans) { clearTimeout(room.timer); rooms.delete(room.code); return [200, { ok: true }]; }
    broadcast(room);
    schedule(room);
    return [200, { ok: true }];
  }
};

function stream(req, res, url) {
  const room = rooms.get(url.searchParams.get('code') || '');
  const token = url.searchParams.get('token') || '';
  if (!room || !room.players.has(token)) { res.writeHead(404); return res.end(); }
  res.writeHead(200, {
    'Content-Type': 'text/event-stream; charset=utf-8',
    'Cache-Control': 'no-cache, no-transform',
    'Connection': 'keep-alive',
    'X-Accel-Buffering': 'no'
  });
  res.write('retry: 2000\n\n');
  if (!room.streams.has(token)) room.streams.set(token, new Set());
  room.streams.get(token).add(res);
  broadcast(room);
  schedule(room);
  const hb = setInterval(() => res.write(': ping\n\n'), 20000);
  req.on('close', () => {
    clearInterval(hb);
    const set = room.streams.get(token);
    if (set) { set.delete(res); if (!set.size) room.streams.delete(token); }
    if (rooms.has(room.code)) { broadcast(room); schedule(room); }
  });
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  try {
    if (url.pathname === '/api/stream') return stream(req, res, url);
    if (url.pathname === '/api/check') {
      const room = rooms.get(url.searchParams.get('code') || '');
      const ok = !!(room && room.players.has(url.searchParams.get('token') || ''));
      return json(res, ok ? 200 : 404, { ok });
    }
    if (url.pathname.startsWith('/api/') && req.method === 'POST') {
      const name = url.pathname.slice(5);
      const fn = api[name];
      if (!fn) return json(res, 404, { error: 'غير موجود' });
      const b = await readBody(req);
      let room = null;
      if (!['create', 'join'].includes(name)) {
        room = rooms.get(String(b.code || ''));
        if (!room || !room.players.has(b.token)) return json(res, 404, { error: 'الغرفة انتهت أو ما أنت فيها.' });
      }
      const [code, out] = await fn(b, room, b.token);
      return json(res, code, out);
    }
    // الملفات
    let file = url.pathname === '/' ? '/index.html' : decodeURIComponent(url.pathname);
    file = path.normalize(file).replace(/^(\.\.[/\\])+/, '');
    const full = path.join(PUB, file);
    if (!full.startsWith(PUB) || !fs.existsSync(full) || fs.statSync(full).isDirectory()) { res.writeHead(404); return res.end('Not found'); }
    res.writeHead(200, { 'Content-Type': MIME[path.extname(full)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
    fs.createReadStream(full).pipe(res);
  } catch (err) {
    console.error(err);
    if (!res.headersSent) json(res, 500, { error: 'صار خطأ في السيرفر.' });
  }
});

// تنظيف الغرف القديمة
setInterval(() => {
  const now = Date.now();
  for (const [code, room] of rooms) {
    if (now - room.touched > 3 * 3600 * 1000 && !room.streams.size) { clearTimeout(room.timer); rooms.delete(code); }
  }
}, 10 * 60 * 1000);

server.listen(PORT, () => console.log(`Domino server on http://localhost:${PORT}`));
