# ooo_sim.py
# Minimal Out-of-Order simulator for a tiny core
# - Rename (RAT + free phys), ROB (in-order commit), simple IQ scheduling
# - Units: 1x ALU (ADD, latency=1), 1x MDU (MUL, latency=3)
# - Issue/Commit width = 2
# - Dispatch (rename) = 1 inst/cycle
# Optional: set PLOT=True for a simple Gantt

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
import math

PLOT = False  # True -> matplotlib Gantt
TRY_PANDAS = True  # Tablo yazdırmada pandas kullan (opsiyonel)

# ---------- Workload ----------
INSTRS = [
    ("MUL", ["R1","R2"], "R3"),
    ("ADD", ["R3","R4"], "R5"),
    ("ADD", ["R2","R6"], "R7"),
    ("ADD", ["R8","R9"], "R10"),
    ("MUL", ["R7","R10"], "R11"),
    ("ADD", ["R5","R11"], "R5"),
]

# ---------- μarch params ----------
LAT   = {"ADD":1, "MUL":3}
FU    = {"ADD":"ALU", "MUL":"MDU"}
UNITS = {"ALU":1, "MDU":1}
ISSUE_WIDTH  = 2
COMMIT_WIDTH = 2
DISPATCH_PER_CYCLE = 1

# ---------- Data types ----------
@dataclass
class Inst:
    idx: int
    op: str
    src_arch: List[str]
    dst_arch: str
    src_phys: List[str]=field(default_factory=list)
    dst_phys: str=""
    rob_idx: int=0
    dispatch_cycle: int=0
    issue_cycle: Optional[int]=None
    fu: Optional[str]=None
    start_exec: Optional[int]=None
    end_exec: Optional[int]=None
    wb_cycle: Optional[int]=None
    commit_cycle: Optional[int]=None

# ---------- Build initial RAT / Free list ----------
def build_rat(n_arch: int = 64) -> Tuple[Dict[str,str], List[str], Dict[str,int]]:
    rat = {f"R{i}": f"p{i}" for i in range(1, n_arch+1)}
    free = [f"p{i}" for i in range(n_arch+1, 512)]
    ready = {f"p{i}":0 for i in range(1, n_arch+1)}  # old phys ready at t=0
    return rat, free, ready

# ---------- Sim ----------
def simulate(instrs: List[Tuple[str,List[str],str]]):
    rat, free_phys, ready_time = build_rat()
    # Dispatch (rename) in order, 1/cycle
    instructions: List[Inst] = []
    rat_rows = []
    cycle = 1
    for i, (op, srcs, dst) in enumerate(instrs, start=1):
        dc = cycle
        # sources by current RAT
        src_p = [rat[s] for s in srcs]
        # allocate new phys for dest
        dst_p = free_phys.pop(0)
        inst = Inst(i, op, srcs, dst, src_p, dst_p, i, dc)
        instructions.append(inst)
        # update RAT & mark new phys "not-ready"
        rat[dst] = dst_p
        ready_time[dst_p] = 10**9
        rat_rows.append({
            "i#": i, "op": op, "dst_arch": dst, "dst_phys": dst_p,
            "src1_arch": srcs[0], "src1_phys": src_p[0],
            "src2_arch": srcs[1], "src2_phys": src_p[1],
            "dispatch_cycle": dc
        })
        cycle += math.ceil(1/DISPATCH_PER_CYCLE)

    # Scheduler state
    inflight = {k:0 for k in UNITS}
    exec_ends: Dict[int, List[Inst]] = {}
    wbs: Dict[int, List[Inst]] = {}
    commit_ptr = 1
    done = False
    cycle = 1

    def ready(inst: Inst, t: int) -> bool:
        return all(ready_time.get(p, 10**9) <= t for p in inst.src_phys)

    # Main loop
    while not done and cycle < 1000:
        # Exec end -> free + schedule WB same cycle
        for inst in exec_ends.pop(cycle, []):
            inflight[inst.fu] -= 1
            wbs.setdefault(cycle, []).append(inst)
        # Perform WB
        for inst in wbs.pop(cycle, []):
            ready_time[inst.dst_phys] = cycle
            inst.wb_cycle = cycle
        # Issue (up to ISSUE_WIDTH)
        issued = 0
        for inst in instructions:
            if inst.issue_cycle is not None:   # already issued
                continue
            unit = FU[inst.op]
            if inflight[unit] >= UNITS[unit]:
                continue
            if inst.dispatch_cycle > cycle:
                continue
            if not ready(inst, cycle):
                continue
            # grant
            inst.issue_cycle = cycle
            inst.fu = unit
            inst.start_exec = cycle
            inst.end_exec = cycle + LAT[inst.op]
            inflight[unit] += 1
            exec_ends.setdefault(inst.end_exec, []).append(inst)
            issued += 1
            if issued >= ISSUE_WIDTH:
                break
        # Commit (in-order)
        committed = 0
        while committed < COMMIT_WIDTH and commit_ptr <= len(instructions):
            head = instructions[commit_ptr-1]
            if head.wb_cycle is not None and head.wb_cycle <= cycle:
                head.commit_cycle = cycle
                commit_ptr += 1
                committed += 1
            else:
                break
        # Termination
        done = all(x.commit_cycle is not None for x in instructions)
        cycle += 1

    return instructions, rat_rows

def print_results(instructions: List[Inst], rat_rows: List[Dict]):
    try:
        import pandas as pd
        if TRY_PANDAS:
            rat_df = pd.DataFrame(rat_rows)
            tl = []
            for inst in instructions:
                tl.append({
                    "i#": inst.idx,
                    "instr": f"{inst.op} {', '.join(inst.src_arch)} -> {inst.dst_arch}",
                    "src_phys": f"{inst.src_phys[0]}, {inst.src_phys[1]}",
                    "dst_phys": inst.dst_phys,
                    "dispatch": inst.dispatch_cycle,
                    "issue": inst.issue_cycle,
                    "start_exec": inst.start_exec,
                    "end_exec": inst.end_exec,
                    "writeback": inst.wb_cycle,
                    "commit": inst.commit_cycle,
                    "FU": inst.fu
                })
            tl_df = pd.DataFrame(tl).set_index("i#")
            print("\n=== RAT at dispatch ===")
            print(rat_df.to_string(index=False))
            print("\n=== Execution timeline (cycles) ===")
            print(tl_df.to_string())
        else:
            raise ImportError
    except Exception:
        # Plain printing
        print("\n=== RAT at dispatch ===")
        for r in rat_rows:
            print(r)
        print("\n=== Execution timeline (cycles) ===")
        for inst in instructions:
            print(vars(inst))

def plot_gantt(instructions: List[Inst]):
    import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(9, 4))
    for i, inst in enumerate(instructions, start=1):
        if inst.start_exec is not None and inst.end_exec is not None:
            ax.barh(i, inst.end_exec - inst.start_exec, left=inst.start_exec, height=0.4)
        if inst.wb_cycle is not None:
            ax.plot(inst.wb_cycle, i, marker='o')
        if inst.commit_cycle is not None:
            ax.plot(inst.commit_cycle, i, marker='s')
    ax.set_yticks(list(range(1, len(instructions)+1)))
    ax.set_yticklabels([f"i{i}: {instructions[i-1].op}" for i in range(1, len(instructions)+1)])
    ax.set_xlabel("Cycle")
    ax.set_title("OoO Execution Gantt (bars=exec, o=WB, s=Commit)")
    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    instrs, rat = simulate(INSTRS)
    print_results(instrs, rat)
    if PLOT:
        plot_gantt(instrs)
