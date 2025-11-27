/* ============================================================
   PipelineLens Modular Core — core.js
   Yönetim: pipeline state + simülasyon adımları
   ============================================================ */

console.log("core.js loaded.");

/* === CONFIG === */
const LAT = { ADD: 1, MUL: 6 };
const FU = { ADD: "ALU", MUL: "MDU" };
const UNITS = { ALU: 1, MDU: 1 };
const ISSUE_WIDTH = 2;
const COMMIT_WIDTH = 2;
const ARCH_N = 64;
const PRF_MAX = 256;

/* === GLOBAL STATE === */
let S = null;
let HIST = [];
let autoTimer = null;

/* === INIT === */
function parseProgram(text) {
  const lines = text.split(/[\r\n]+/).map(s => s.trim()).filter(Boolean);
  const out = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const m = line.match(/^([A-Z]+)\s+([Rr]\d+)\s*,\s*([Rr]\d+)\s*->\s*([Rr]\d+)$/);
    if (!m) throw new Error(`Line ${i + 1}: bad syntax "${line}"`);
    const op = m[1].toUpperCase();
    if (!(op in FU)) throw new Error(`Line ${i + 1}: unsupported OP "${op}"`);
    out.push({ idx: i + 1, op, src: ["R" + (+m[2].slice(1)), "R" + (+m[3].slice(1))], dst: "R" + (+m[4].slice(1)) });
  }
  return out;
}

/* === STATE CREATION === */
function buildInitialState(program) {
  const fmap = {}, amap = {}, free = [], prf = {}, prfReady = {};
  for (let i = 1; i <= ARCH_N; i++) {
    const p = "p" + i;
    fmap["R" + i] = p;
    amap["R" + i] = p;
    prf[p] = 0;
    prfReady[p] = true;
  }
  for (let j = ARCH_N + 1; j <= PRF_MAX; j++) free.push("p" + j);

  return {
    cycle: 0,
    prog: program,
    fmap,
    amap,
    free,
    prf,
    prfReady,
    prfAllocCount: 0,
    ROB: [],
    RS: [],
    inflight: { ALU: 0, MDU: 0 },
    execEnds: {},
    log: [],
    commitPtr: 0,
    metrics: { ticks: 0, comm: 0, alu: 0, mdu: 0 }
  };
}

/* === RENAME === */
function renameOne(state, inst) {
  const s1 = state.fmap[inst.src[0]];
  const s2 = state.fmap[inst.src[1]];
  const old = state.fmap[inst.dst];
  const dstP = state.free.shift();
  state.fmap[inst.dst] = dstP;
  state.prfReady[dstP] = false;
  state.prf[dstP] = 0;
  state.prfAllocCount++;

  const rsEntry = { idx: inst.idx, op: inst.op, s1, s2, d: dstP, fu: FU[inst.op], issued: false, start: null, end: null, done: false };
  state.RS.push(rsEntry);
  state.ROB.push({ idx: inst.idx, op: inst.op, dst: dstP, old: old, wb: false, commit: false });

  return { line: `i${inst.idx}: ${inst.op} ${inst.src[0]},${inst.src[1]} -> ${inst.dst} | ${s1},${s2} -> ${dstP} (old ${old})` };
}

function renameAll(state) {
  const logs = [];
  for (let i = 0; i < state.prog.length; i++) logs.push(renameOne(state, state.prog[i]).line);
  return logs;
}

/* === EXECUTION === */
function canIssue(entry, state) {
  return (
    state.prfReady[entry.s1] &&
    state.prfReady[entry.s2] &&
    !entry.issued &&
    state.inflight[entry.fu] < UNITS[entry.fu]
  );
}

function startExec(entry, state, t) {
  entry.issued = true;
  entry.start = t;
  entry.end = t + LAT[entry.op];
  state.inflight[entry.fu]++;
  const v1 = state.prf[entry.s1];
  const v2 = state.prf[entry.s2];
  entry.result = entry.op === "ADD" ? v1 + v2 : v1 * v2;
  (state.execEnds[entry.end] = state.execEnds[entry.end] || []).push(entry);
  state.log.push(`Issue@t${t}: i${entry.idx} -> ${entry.fu}`);
}

function writebackAllDue(state, t) {
  const ended = state.execEnds[t] || [];
  for (let e of ended) {
    state.inflight[e.fu]--;
    state.prf[e.d] = e.result;
    state.prfReady[e.d] = true;
    e.done = true;
    const rob = state.ROB.find(r => r.idx === e.idx);
    rob.wb = true;
    state.log.push(`WB@t${t}: i${e.idx} -> ${e.d} = ${e.result}`);
  }
  delete state.execEnds[t];
}

function tryCommit(state, t) {
  let committed = 0;
  while (committed < COMMIT_WIDTH && state.commitPtr < state.ROB.length) {
    const head = state.ROB[state.commitPtr];
    if (head.wb) {
      head.commit = true;
      state.amap[state.prog[head.idx - 1].dst] = head.dst;
      state.free.push(head.old);
      state.prfAllocCount--;
      state.commitPtr++;
      committed++;
      state.metrics.comm++;
      state.log.push(`Commit@t${t}: i${head.idx} (free ${head.old})`);
    } else break;
  }
}

/* === STEP === */
function step(state) {
  const t = state.cycle + 1;
  state.log = [];

  writebackAllDue(state, t);
  let issued = 0;
  for (let e of state.RS) {
    if (canIssue(e, state)) {
      startExec(e, state, t);
      issued++;
      if (issued >= ISSUE_WIDTH) break;
    }
  }
  tryCommit(state, t);

  state.cycle = t;
  state.metrics.ticks++;
  if (state.inflight.ALU > 0) state.metrics.alu++;
  if (state.inflight.MDU > 0) state.metrics.mdu++;
}

/* === UI UTILS === */
function showToast(lines) {
  if (!lines || !lines.length) return;
  const d = document.createElement("div");
  d.className = "toast";
  d.innerHTML = lines.join("<br>");
  document.body.appendChild(d);
  setTimeout(() => d.remove(), 2600);
}

/* === RENDER === */
function renderAll() {
  if (typeof renderRS === "function") renderRS(S);
  if (typeof renderROB === "function") renderROB(S);
  if (typeof renderPRF === "function") renderPRF(S);
  if (typeof renderRAT === "function") renderRAT(S);

  const logDiv = document.getElementById("log");
  if (logDiv) logDiv.innerHTML = S.log.map(x => "• " + x).join("<br>") || "—";
}

/* === CONTROL === */
function resetFromProgram() {
  const progTxt = document.getElementById("prog").value;
  let prog;
  try { prog = parseProgram(progTxt); } catch (e) { alert(e.message); return; }
  S = buildInitialState(prog);
  const logs = renameAll(S);
  HIST = [JSON.parse(JSON.stringify(S))];
  console.log("Program yüklendi, rename tamamlandı.");
  renderAll();
}

function onStep() {
  const before = S.log.length;
  step(S);
  HIST.push(JSON.parse(JSON.stringify(S)));
  renderAll();
  const lines = S.log.slice(before);
  if (lines.length) {
    const expl = [];
    for (let L of lines) {
      let E = L;
      if (L.startsWith("Issue@t")) E += " — RS→FU (hazır operandlar)";
      if (L.startsWith("WB@t")) E += " — PRF’e yazıldı";
      if (L.startsWith("Commit@t")) E += " — arch_map güncellendi";
      expl.push(E);
    }
    showToast(expl);
  }
}

function applyAuto(run) {
  const btn = document.getElementById("btnAuto");
  if (run) {
    if (autoTimer) return;
    btn.textContent = "Pause ❚❚";
    const spd = +document.getElementById("speed").value;
    autoTimer = setInterval(() => {
      onStep();
      if (S.commitPtr >= S.ROB.length) applyAuto(false);
    }, spd);
  } else {
    btn.textContent = "Auto ▷";
    clearInterval(autoTimer);
    autoTimer = null;
  }
}

/* === THEME === */
function setTheme(theme) {
  document.documentElement.dataset.theme = theme;
  try { localStorage.setItem("pl_theme", theme); } catch (e) {}
}
function toggleTheme() {
  const cur = document.documentElement.dataset.theme || "dark";
  setTheme(cur === "dark" ? "light" : "dark");
}

/* === EVENT BINDINGS === */
window.addEventListener("DOMContentLoaded", () => {
  document.getElementById("btnLoad").onclick = resetFromProgram;
  document.getElementById("btnReset").onclick = resetFromProgram;
  document.getElementById("btnStep").onclick = onStep;
  document.getElementById("btnAuto").onclick = () => applyAuto(!autoTimer);
  document.getElementById("btnTheme").onclick = toggleTheme;
  document.getElementById("btnOpenRename").onclick = () => openRename(S);

  let saved = "dark";
  try { saved = localStorage.getItem("pl_theme") || "dark"; } catch (e) {}
  document.documentElement.dataset.theme = saved;

  // İlk yükleme
  setTimeout(() => { if (!S) resetFromProgram(); }, 400);
});
