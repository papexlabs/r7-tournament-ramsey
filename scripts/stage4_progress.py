"""Stage 4 progress from the synced results (Mac or server), against the projection.

For every instance under results/stage4/: level-0 cubes closed (UNSAT VERIFIED, directly
or through all of their children), cube records, SAT cubes, failed checks, solver
hours so far (wall seconds of finished cubes, server time) and the projected
vCPU-hours from data/stage4_manifest.json.
usage: python3 scripts/stage4_progress.py [RESULTS_DIR]
"""
import json
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
res = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "results/stage4"
man = json.loads((ROOT / "data/stage4_manifest.json").read_text())["instances"]


def closed(cid, latest, kids):
    r = latest.get(cid)
    if r is None:
        return False
    if r["status"] == "UNSAT":
        return r.get("check") == "VERIFIED"
    if r["status"] != "UNKNOWN":
        return False
    ch = kids.get(cid, [])
    S = len(latest[ch[0]]["lits"]) - len(r["lits"]) if ch else 0
    return bool(ch) and len(ch) == 1 << S and all(closed(c, latest, kids) for c in ch)


tot_h = tot_p = 0.0
print(f"{'instance':12} {'L0 closed':>10} {'records':>7} {'SAT':>3} {'fail':>4} {'server h':>8} {'at this rate':>12} "
      f"{'proj vCPU-h':>11} {'summary':>11}")
for d in sorted(p for p in res.glob("*") if p.is_dir()):
    name = d.name
    rj = d / "run/results.jsonl"
    latest = {}
    if rj.exists():
        for line in rj.read_text().splitlines():
            r = json.loads(line)
            latest[r["id"]] = r
    kids = defaultdict(list)
    for cid in latest:
        if "." in cid:
            kids[cid.rsplit(".", 1)[0]].append(cid)
    n0 = sum(1 for l in (d / "cubes.icnf").read_text().splitlines() if l.startswith("a ")) if (d / "cubes.icnf").exists() else 0
    c0 = sum(closed(str(i), latest, kids) for i in range(n0))
    sat = sum(r["status"] == "SAT" for r in latest.values())
    fail = sum(r["status"] == "UNSAT" and r.get("check") != "VERIFIED" for r in latest.values())
    h = sum(r["secs"] for r in latest.values()) / 3600
    p = man.get(name, {}).get("expected_vcpu_h", 0)
    s = d / "run/summary.json"
    verdict = json.loads(s.read_text())["verdict"] if s.exists() else "-"
    tot_h += h
    tot_p += p
    rate = h * n0 / c0 if c0 else float("nan")
    print(f"{name:12} {c0:5d}/{n0:<4d} {len(latest):7d} {sat:3d} {fail:4d} {h:8.1f} {rate:12.1f} {p:11.1f} {verdict:>11}")
print(f"{'total':12} {'':10} {'':7} {'':3} {'':4} {tot_h:8.1f} {tot_p:11.1f}")
print("'at this rate' = server hours / fraction of level-0 cubes closed (biased high early: hard cubes")
print("stay open longest).  Stop rule: total server hours above 2x the sum of the projections -> stop and report.")
