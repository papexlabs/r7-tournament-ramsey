"""Run cadical / kissat on a CNF with a time limit (nice 10); log and record.

usage: run_sat.py NAME CNF {cadical,kissat} SECONDS [--lrat] [--opts "..."]

Appends one line to results/runs.csv:
 name,solver,opts,status,seconds,conflicts,lrat_check,proof_bytes,host,date
With --lrat (cadical only) a text LRAT proof is written to proofs/NAME.lrat,
checked with build/lrat-check, its size recorded, and the file deleted.
"""

import argparse
import csv
import datetime
import os
import platform
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from stream_solve import lrat_verdict  # noqa: E402  (exit code AND output, see its comment)
LOGS = ROOT / "results/logs"
LOGS.mkdir(parents=True, exist_ok=True)
(ROOT / "proofs").mkdir(exist_ok=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("name")
    ap.add_argument("cnf")
    ap.add_argument("solver", choices=["cadical", "kissat"])
    ap.add_argument("seconds", type=int)
    ap.add_argument("--lrat", action="store_true")
    ap.add_argument("--opts", default="")
    ap.add_argument("--keep-proof", action="store_true")
    a = ap.parse_args()

    opts = a.opts.replace("_", " ").split()
    proof = None
    if a.solver == "cadical":
        cmd = ["nice", "-n", "10", "cadical", "-t", str(a.seconds)] + opts + [a.cnf]
        if a.lrat:
            proof = ROOT / f"proofs/{a.name}.lrat"
            cmd = ["nice", "-n", "10", "cadical", "-t", str(a.seconds), "--lrat=true",
                   "--binary=false"] + opts + [a.cnf, str(proof)]
    else:
        cmd = ["nice", "-n", "10", "kissat", f"--time={a.seconds}"] + opts + [a.cnf]
    log = LOGS / f"{a.name}.{a.solver}.log"
    t0 = time.time()
    with open(log, "w") as fh:
        fh.write("c cmd: " + " ".join(cmd) + "\n")
        fh.flush()
        rc = subprocess.run(cmd, stdout=fh, stderr=subprocess.STDOUT).returncode
    wall = time.time() - t0
    txt = log.read_text()
    status = {10: "SAT", 20: "UNSAT"}.get(rc, "UNKNOWN")
    m = re.search(r"total process time since initialization:\s+([\d.]+)", txt) or \
        re.search(r"process-time:\s+(?:\S+\s+)?([\d.]+)\s+seconds", txt)
    secs = float(m.group(1)) if m else round(wall, 2)
    m = re.search(r"^c conflicts:\s+(\d+)", txt, re.M)
    conf = int(m.group(1)) if m else -1
    check, pbytes = "", ""
    if proof is not None and proof.exists():
        pbytes = proof.stat().st_size
        if status == "UNSAT":
            t1 = time.time()
            r = subprocess.run(["nice", "-n", "10", str(ROOT / "build/lrat-check"), a.cnf, str(proof)],
                               capture_output=True, text=True)
            verdict = lrat_verdict(r.returncode, r.stdout + r.stderr)
            check = f"{verdict}({time.time()-t1:.1f}s)"
            with open(log, "a") as fh:
                fh.write("c lrat-check output:\n" + r.stdout[-2000:] + r.stderr[-2000:])
        if not a.keep_proof:
            proof.unlink()
    row = [a.name, a.solver, a.opts, status, f"{secs:.2f}", conf, check, pbytes,
           platform.node().split(".")[0] and "mac-m5", datetime.datetime.now().isoformat(timespec="seconds")]
    csvp = ROOT / "results/runs.csv"
    new = not csvp.exists()
    with open(csvp, "a", newline="") as fh:
        w = csv.writer(fh)
        if new:
            w.writerow(["name", "solver", "opts", "status", "seconds", "conflicts", "lrat_check",
                        "proof_bytes", "host", "date"])
        w.writerow(row)
    print(",".join(str(x) for x in row))


if __name__ == "__main__":
    main()
