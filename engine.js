// محرك الضومنة المشترك بين السيرفر والصفحة (مستخرج من الصفحة)
'use strict';
/* ---------- أدوات ---------- */
const sum = a => a.reduce((s, x) => s + x, 0);
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const sleep = ms => new Promise(r => setTimeout(r, ms));
const pips = t => t[0] + t[1];
const isDouble = t => t[0] === t[1];
const has = (t, v) => t[0] === v || t[1] === v;
const key = t => Math.min(t[0], t[1]) + '-' + Math.max(t[0], t[1]);
const fmt = t => `[${t[0]}|${t[1]}]`;
const uniq = a => [...new Set(a)];
const plural = (n, one, many) => `${n} ${n === 1 ? one : many}`;

/* ---------- الأحجار ---------- */
function fullSet() { const s = []; for (let a = 0; a <= 6; a++) for (let b = a; b <= 6; b++) s.push([a, b]); return s; }
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }

let G = null;
function __setG(g) { G = g; }
function ends(board = G.board) { return board.length ? [board[0][0], board[board.length - 1][1]] : null; }

function legalMoves(hand, board, forced) {
  const res = [];
  if (!board.length) {
    for (const t of hand) if (!forced || key(t) === key(forced)) res.push({ t, side: 'R' });
    return res;
  }
  const [L, R] = ends(board);
  for (const t of hand) {
    if (has(t, L)) res.push({ t, side: 'L' });
    if (has(t, R) && !(L === R)) res.push({ t, side: 'R' });
  }
  return res;
}

function place(board, t, side) {
  const b = board.slice();
  if (!b.length) { b.push([t[0], t[1]]); return b; }
  if (side === 'L') { const L = b[0][0]; b.unshift(t[1] === L ? [t[0], t[1]] : [t[1], t[0]]); }
  else { const R = b[b.length - 1][1]; b.push(t[0] === R ? [t[0], t[1]] : [t[1], t[0]]); }
  return b;
}

/* =========================================================
   المحرك الذكي (للمحترف والمدرّب، لاعبين أو أربعة)
   1) يعدّ كل رقم من 0 إلى 6: كم نزل، كم معك، كم باقي مجهول
   2) يتابع كل لاعب: كل ما سحب أو مرّر ينحفظ إنه ما عنده أرقام الأطراف
   3) يولّد مئات التوزيعات الممكنة لأحجار الباقين تتوافق مع هالمعلومات
   4) يكمّل الجولة لكل حركة في كل توزيعة، وكل لاعب في المحاكاة ما يشوف أحجار غيره
   5) في آخر الجولة يحسب كل الاحتمالات حساب كامل
   6) يختار الحركة اللي تعطي فريقك أعلى نقاط متوقعة وأعلى فرصة فوز
   ========================================================= */
const TILES = fullSet();
const TID = {};
TILES.forEach((t, i) => { TID[key(t)] = i; });
const TA = TILES.map(t => t[0]), TB = TILES.map(t => t[1]), TP = TILES.map(pips);
const TBITS = TILES.map(t => (1 << t[0]) | (1 << t[1]));
const tid = t => TID[key(t)];
const hasId = (i, v) => TA[i] === v || TB[i] === v;
const otherEnd = (i, v) => (TA[i] === v ? TB[i] : TA[i]);
const popc = m => { let c = 0; while (m) { c += m & 1; m >>= 1; } return c; };
const sumIds = h => { let s = 0; for (const i of h) s += TP[i]; return s; };
const teamSums = h => { const s = [0, 0]; h.forEach((x, q) => { s[q % 2] += sumIds(x); }); return s; };

/* --- وش ينعرف عن يد كل لاعب --- */
function knowDraw(p, e, drew, playable) {
  const m = (1 << e[0]) | (1 << e[1]);
  const sl = G.slots[p];
  for (let i = 0; i < sl.length; i++) sl[i] |= m;
  for (let k = 0; k < drew; k++) sl.push(k === drew - 1 && playable ? 0 : m);
}
function knowPlay(p, t) {
  const sl = G.slots[p];
  if (!sl.length) return;
  const bits = TBITS[tid(t)];
  let pick = -1, best = -1;
  for (let i = 0; i < sl.length; i++) if (!(sl[i] & bits) && popc(sl[i]) > best) { best = popc(sl[i]); pick = i; }
  if (pick < 0) for (let i = 0; i < sl.length; i++) if (popc(sl[i]) > best) { best = popc(sl[i]); pick = i; }
  sl.splice(pick, 1);
}
function knownVoid(p, v) { const sl = G.slots[p]; return !!sl && sl.length > 0 && sl.every(m => m & (1 << v)); }

// عدّاد الأرقام من وجهة نظر اللاعب o
function suitCounts(o, board = G.board, hand = G.hands[o]) {
  const out = [], N = G.n, nx = (o + 1) % N;
  for (let v = 0; v <= 6; v++) {
    let b = 0, h = 0;
    for (const t of board) if (has(t, v)) b++;
    for (const t of hand) if (has(t, v)) h++;
    const voids = [];
    for (let q = 0; q < N; q++) if (q !== o && knownVoid(q, v)) voids.push(q);
    const oppVoidAll = N === 2 ? knownVoid(1 - o, v) : (knownVoid((o + 1) % 4, v) && knownVoid((o + 3) % 4, v));
    out.push({ v, board: b, mine: h, unknown: 7 - b - h, voids, nextVoid: knownVoid(nx, v), void: oppVoidAll });
  }
  return out;
}

/* --- توزيعة محتملة لأحجار الباقين --- */
function sampleWorld(o) {
  const N = G.n;
  const known = new Uint8Array(28);
  for (const t of G.board) known[tid(t)] = 1;
  for (const t of G.hands[o]) known[tid(t)] = 1;
  const pool = [];
  for (let i = 0; i < 28; i++) if (!known[i]) pool.push(i);
  const slots = [];
  for (let q = 0; q < N; q++) {
    if (q === o) continue;
    const sl = G.slots[q];
    for (let i = 0; i < G.hands[q].length; i++) slots.push({ q, m: sl[i] || 0 });
  }
  slots.sort((a, b) => popc(b.m) - popc(a.m));
  for (let attempt = 0; ; attempt++) {
    shuffle(pool);
    const used = new Uint8Array(28), hands = Array.from({ length: N }, () => []);
    let ok = true;
    for (const s of slots) {
      const m = attempt < 20 ? s.m : 0;
      let found = -1;
      for (const id of pool) if (!used[id] && !(TBITS[id] & m)) { found = id; break; }
      if (found < 0) { ok = false; break; }
      used[found] = 1;
      hands[s.q].push(found);
    }
    if (ok) return { hands, bone: pool.filter(id => !used[id]) };
  }
}

/* --- محاكاة سريعة --- */
function simMoves(st, p) {
  const res = [];
  for (const id of st.h[p]) {
    if (st.empty) { res.push(id, 1); continue; }
    if (hasId(id, st.L)) res.push(id, 0);
    if (st.L !== st.R && hasId(id, st.R)) res.push(id, 1);
  }
  return res;
}
function simApply(st, p, id, side) {
  const h = st.h[p];
  h.splice(h.indexOf(id), 1);
  st.cnt[TA[id]]++;
  if (TB[id] !== TA[id]) st.cnt[TB[id]]++;
  st.vd[p] &= ~TBITS[id];
  if (st.empty) { st.L = TA[id]; st.R = TB[id]; st.empty = false; }
  else if (side === 0) st.L = otherEnd(id, st.L);
  else st.R = otherEnd(id, st.R);
}
function canPlay(h, L, R) { for (const id of h) if (hasId(id, L) || hasId(id, R)) return true; return false; }

// كل لاعب في المحاكاة يقرر بالمعلومات اللي يعرفها بس
function policy(st, p, mv) {
  if (mv.length === 2) return 0;
  const N = st.n, me = st.h[p];
  const vdN = st.vd[(p + 1) % N], vdM = N === 4 ? st.vd[(p + 2) % 4] : 0;
  const unkW = N === 4 ? 0.3 : 0.5;
  const mine = [0, 0, 0, 0, 0, 0, 0];
  for (const x of me) { mine[TA[x]]++; if (TB[x] !== TA[x]) mine[TB[x]]++; }
  let best = 0, bs = -1e9;
  for (let k = 0; k < mv.length; k += 2) {
    const id = mv[k], side = mv[k + 1];
    if (me.length === 1) return k;
    const nL = side === 0 ? otherEnd(id, st.L) : st.L;
    const nR = side === 1 ? otherEnd(id, st.R) : st.R;
    let s = TP[id] * 0.5 + (TA[id] === TB[id] ? 3 : 0) + Math.random() * 1.2;
    let sup = 0;
    for (const x of me) if (x !== id && (hasId(x, nL) || hasId(x, nR))) sup++;
    s += Math.min(sup, 3) * 1.6;
    let blocked = true;
    for (const v of (nL === nR ? [nL] : [nL, nR])) {
      const hv = hasId(id, v) ? 1 : 0;
      const unk = 7 - (st.cnt[v] + hv) - (mine[v] - hv);
      if (unk <= 0 || (vdN & (1 << v))) s += 3; else { blocked = false; s -= unk * unkW; }
      if (vdM & (1 << v)) s -= 1.5;
    }
    if (blocked) s += 6;
    if (s > bs) { bs = s; best = k; }
  }
  return best;
}
function lockScore(h, rt) {
  const s = teamSums(h), a = s[rt], b = s[1 - rt];
  return a < b ? b : a > b ? -a : 0;
}
function rollout(st, rt) {
  const N = st.n;
  for (let g = 0; g < 200; g++) {
    const p = st.turn;
    let mv = simMoves(st, p);
    if (!mv.length) {
      const m = (1 << st.L) | (1 << st.R);
      while (!mv.length && st.bone.length) { st.h[p].push(st.bone.pop()); mv = simMoves(st, p); }
      st.vd[p] = mv.length ? m & ~TBITS[mv[0]] & ~TBITS[mv[mv.length - 2]] : m;
      if (!mv.length) {
        if (++st.passes >= N) return lockScore(st.h, rt);
        st.turn = (p + 1) % N;
        continue;
      }
    }
    const k = policy(st, p, mv);
    simApply(st, p, mv[k], mv[k + 1]);
    st.passes = 0;
    if (!st.h[p].length) return (p % 2 === rt ? 1 : -1) * teamSums(st.h)[1 - (p % 2)];
    st.turn = (p + 1) % N;
  }
  return 0;
}

// آخر الجولة (ما فيه سحب): حساب كامل
const ABORT = {};
let nodeBudget = 0;
function solve(L, R, h, p, passes, rt, alpha, beta) {
  if (--nodeBudget < 0) throw ABORT;
  const N = h.length, me = h[p], mv = [];
  for (const id of me) {
    if (hasId(id, L)) mv.push(id, 0);
    if (L !== R && hasId(id, R)) mv.push(id, 1);
  }
  if (!mv.length) {
    if (passes + 1 >= N) return lockScore(h, rt);
    return solve(L, R, h, (p + 1) % N, passes + 1, rt, alpha, beta);
  }
  const maxi = p % 2 === rt;
  let best = maxi ? -1e9 : 1e9;
  for (let k = 0; k < mv.length; k += 2) {
    const id = mv[k], side = mv[k + 1];
    const nh = me.filter(x => x !== id);
    let val;
    if (!nh.length) val = (maxi ? 1 : -1) * teamSums(h)[1 - (p % 2)];
    else {
      const nL = side === 0 ? otherEnd(id, L) : L, nR = side === 1 ? otherEnd(id, R) : R;
      const hh = h.slice(); hh[p] = nh;
      val = solve(nL, nR, hh, (p + 1) % N, 0, rt, alpha, beta);
    }
    if (maxi) { if (val > best) best = val; if (best > alpha) alpha = best; }
    else { if (val < best) best = val; if (best < beta) beta = best; }
    if (alpha >= beta) break;
  }
  return best;
}
function finishSim(st, rt) {
  let total = 0;
  for (const x of st.h) total += x.length;
  if (!st.bone.length && total <= 10) {
    nodeBudget = 6000;
    try { return solve(st.L, st.R, st.h, st.turn, st.passes, rt, -1e9, 1e9); }
    catch (e) { if (e !== ABORT) throw e; }
  }
  return rollout(st, rt);
}

/* --- تحليل كل حركة ممكنة للاعب o --- */
function newJob(o, max) {
  const moves = legalMoves(G.hands[o], G.board, G.forcedFirst);
  return { o, moves, max, samples: 0, runId: G.runId, cancelled: false,
    stats: moves.map(() => ({ n: 0, sum: 0, win: 0, loss: 0, blocked: 0 })) };
}
function jobStep(job, ms) {
  const t0 = performance.now();
  const o = job.o, N = G.n, rt = o % 2, nx = (o + 1) % N;
  const myIds = G.hands[o].map(tid), e = ends();
  const cnt0 = [0, 0, 0, 0, 0, 0, 0];
  for (const t of G.board) { cnt0[t[0]]++; if (t[1] !== t[0]) cnt0[t[1]]++; }
  const vd0 = [];
  for (let q = 0; q < N; q++) { let m = 0; for (let v = 0; v <= 6; v++) if (knownVoid(q, v)) m |= 1 << v; vd0.push(m); }
  do {
    const w = sampleWorld(o);
    job.moves.forEach((mv, i) => {
      const st = {
        n: N, h: w.hands.map((x, q) => (q === o ? myIds.slice() : x.slice())),
        bone: w.bone.slice(), L: e ? e[0] : 0, R: e ? e[1] : 0, empty: !e, turn: o, passes: 0,
        cnt: cnt0.slice(), vd: vd0.slice()
      };
      simApply(st, o, tid(mv.t), mv.side === 'L' ? 0 : 1);
      const s = job.stats[i];
      let score;
      if (!st.h[o].length) score = teamSums(st.h)[1 - rt];
      else {
        if (!canPlay(st.h[nx], st.L, st.R)) s.blocked++;
        st.turn = nx;
        score = finishSim(st, rt);
      }
      s.n++; s.sum += score;
      if (score > 0) s.win++; else if (score < 0) s.loss++;
    });
    job.samples++;
  } while (performance.now() - t0 < ms && job.samples < job.max);
}
async function runJob(job, totalMs) {
  const end = performance.now() + totalMs;
  while (performance.now() < end && job.samples < job.max) {
    if (!G || G.runId !== job.runId || job.cancelled) return job;
    jobStep(job, 25);
    await sleep(0);
  }
  return job;
}
function topUp(job, minSamples, maxMs) {
  const t0 = performance.now();
  job.max = Math.max(job.max, minSamples);
  while (job.samples < minSamples && performance.now() - t0 < maxMs) jobStep(job, 25);
}
function jobResults(job) {
  return job.moves.map((m, i) => {
    const s = job.stats[i], n = Math.max(1, s.n);
    const avg = s.sum / n, win = s.win / n, loss = s.loss / n;
    return { m, avg, win, loss, blocked: s.blocked / n, n: s.n, value: avg + 12 * (win - loss) };
  }).sort((a, b) => b.value - a.value || pips(b.m.t) - pips(a.m.t));
}


this.E = { __setG, fullSet, shuffle, legalMoves, place, ends, key, pips, sum, uniq, isDouble, knowDraw, knowPlay, newJob, jobStep, jobResults };
