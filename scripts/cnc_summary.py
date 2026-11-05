"""Certificate summary for a run_cubes.py run.

Checks, from DIR/results.jsonl:
 1. Level-0 cover: CNF-free check that the ICNF cubes cover every assignment:
    the clauses (not c_i) must be UNSAT; proved by CaDiCaL with LRAT and
    verified by lrat-check (works for any cube set, also march cubes; if the
    cubes alone are not a cover it falls back to CNF + (not c_i), which needs
    the CNF).
 2. Every split cube was replaced by children that are exactly the 2^S sign
    patterns of S fresh variables appended to the parent (structural check).
 3. Every leaf (cube without children) has status UNSAT with check VERIFIED.
 4. Every level-0 record solved exactly its cube: its literals equal the matching 'a' line of
    ICNF (the record of cube i has id "i").
 5. If DIR/body.sha256 exists (written by run_cubes.py with body.cnf), it is reported as
    body_sha256, and body.cnf, if present, must still have that hash.
Prints ALL CLOSED only if 1-5 hold and no SAT cube exists.
usage: cnc_summary.py CNF ICNF DIR
"""
import json
import os
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from stream_solve import stream_solve  # noqa: E402
from run_cubes import read_cubes, sha256_file  # noqa: E402


def cover_check(cubes, nvars, cnf_body=None, ncnf=0):
    wd = tempfile.mkdtemp(prefix="cover_")
    empty = Path(wd) / "empty.cnf"
    empty.write_text("")
    neg = [" ".join(str(-l) for l in c) + " 0" for c in cubes]
    r = stream_solve(str(empty), nvars, 0, neg, wd, "cubesonly", check=True)
    if r["status"] == "UNSAT":
        return "VERIFIED (cubes alone)" if r.get("check") == "VERIFIED" else "CHECK FAILED"
    if cnf_body is None:
        return "NOT A COVER WITHOUT THE CNF"
    r = stream_solve(cnf_body, nvars, ncnf, neg, wd, "withcnf", check=True)
    if r["status"] == "UNSAT":
        return "VERIFIED (with CNF)" if r.get("check") == "VERIFIED" else "CHECK FAILED"
    return "NOT A COVER"


def main():
    cnf, icnf, d = sys.argv[1:4]
    d = Path(d)
    nv, nc = map(int, (d / "body.meta").read_text().split())
    cubes = read_cubes(icnf)
    cov = cover_check(cubes, nv, str(d / "body.cnf"), nc)
    latest = {}
    for line in open(d / "results.jsonl"):
        r = json.loads(line)
        latest[r["id"]] = r
    kids = defaultdict(list)
    for cid in latest:
        if "." in cid:
            kids[cid.rsplit(".", 1)[0]].append(cid)
    problems = []
    open_leaves, verified_leaves, sat = 0, 0, []
    def visit(cid, lits):
        nonlocal open_leaves, verified_leaves
        r = latest.get(cid)
        if r is None:
            open_leaves += 1
            return
        if r.get("lits") != lits:  # level 0: lits is the ICNF cube (deeper ids pass their own lits)
            problems.append(f"{cid}: record literals differ from cube {cid} of the ICNF")
        if r["status"] == "SAT":
            sat.append(cid)
            return
        if r["status"] == "UNSAT":
            if r.get("check") == "VERIFIED":
                verified_leaves += 1
            else:
                problems.append(f"{cid} UNSAT but check={r.get('check')}")
            return
        ch = kids.get(cid, [])
        if not ch:
            open_leaves += 1
            return
        S = len(latest[ch[0]]["lits"]) - len(lits)
        pats = {}
        for c in ch:
            cl = latest[c]["lits"]
            if len(cl) != len(lits) + S or cl[: len(lits)] != lits:
                problems.append(f"{c} does not extend {cid} by {S} literals")
                continue
            pats[c] = tuple(cl[len(lits):])
        vsets = {tuple(abs(x) for x in t) for t in pats.values()}
        if len(vsets) > 1 or (vsets and set(next(iter(vsets))) & {abs(y) for y in lits}):
            problems.append(f"children of {cid} do not split on one fresh variable set")
        if len(set(pats.values())) != len(pats):
            problems.append(f"children of {cid} repeat a sign pattern")
        for m in range(1 << S):
            c = f"{cid}.{m}"
            if c not in latest:
                open_leaves += 1
            else:
                visit(c, latest[c]["lits"])

    for i, c in enumerate(cubes):
        visit(str(i), c)
    body_sha = None
    if (d / "body.sha256").exists():
        body_sha = (d / "body.sha256").read_text().split()[0]
        if (d / "body.cnf").exists() and sha256_file(d / "body.cnf") != body_sha:
            problems.append("body.cnf does not match body.sha256")
    secs = sum(r["secs"] for r in latest.values())
    ok = cov.startswith("VERIFIED") and not problems and not sat and open_leaves == 0
    s = {"level0_cubes": len(cubes), "cover": cov, "verified_leaves": verified_leaves,
         "open_leaves": open_leaves, "sat_cubes": sat, "problems": problems[:20],
         "solver_hours": round(secs / 3600, 2), "body_sha256": body_sha, "cubes_sha256": sha256_file(icnf),
         "verdict": "ALL CLOSED" if ok else "NOT CLOSED"}
    (d / "summary.json").write_text(json.dumps(s, indent=1))
    print(json.dumps(s))


if __name__ == "__main__":
    main()
