"""Tiny cube-and-conquer run checked by scripts/cnc_summary.py and scripts/audit/closure.py.

Pigeonhole 10 -> 9 (CaDiCaL needs about 3 s), 4 static cubes, time limits 1 s and 1 s, then no
limit, split 2, so some cubes are split and their children solved (streamed LRAT checks).
 1. run_cubes.py writes body.sha256 = sha256 of the CNF without its header;
 2. cnc_summary.py: ALL CLOSED, cover VERIFIED, body_sha256 reported; closure.py: no problem;
 3. a level-0 record whose literals differ from its ICNF cube: NOT CLOSED (both tools);
 4. body.cnf changed after the run: NOT CLOSED.
Run: python3 tests/test_cnc_summary.py   (needs build/lrat-check and cadical on PATH)
"""
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PY = sys.executable
bad = 0


def check(cond, msg):
    global bad
    print(("ok   " if cond else "FAIL ") + msg, flush=True)
    bad += not cond


def summary(cnf, d):
    r = subprocess.run([PY, "-I", str(ROOT / "scripts/cnc_summary.py"), str(cnf), str(d / "cubes.icnf"), str(d / "run")],
                       capture_output=True, text=True, check=True)
    return json.loads(r.stdout.strip().splitlines()[-1])


def closure(d):
    return subprocess.run([PY, "-I", str(ROOT / "scripts/audit/closure.py"), str(d)], capture_output=True, text=True)


td = Path(tempfile.mkdtemp(prefix="tcnc_"))
try:
    p, h = 10, 9
    x = lambda i, j: i * h + j + 1
    cls = [[x(i, j) for j in range(h)] for i in range(p)]
    cls += [[-x(i, j), -x(k, j)] for j in range(h) for i in range(p) for k in range(i + 1, p)]
    cnf = td / "php.cnf"
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in cls)
    cnf.write_text(f"p cnf {p * h} {len(cls)}\n" + body)
    d = td / "inst"
    d.mkdir()
    subprocess.run([PY, "-I", str(ROOT / "scripts/make_cubes.py"), str(cnf), str(d / "cubes.icnf"), "--k", "2"],
                   check=True, capture_output=True)
    r = subprocess.run([PY, "-I", str(ROOT / "scripts/run_cubes.py"), str(cnf), str(d / "cubes.icnf"), str(d / "run"),
                        "--workers", "3", "--timeouts", "1,1,0", "--split", "2"], capture_output=True, text=True)
    recs = [json.loads(l) for l in (d / "run/results.jsonl").read_text().splitlines()]
    check(r.returncode == 0 and "finished" in r.stdout, f"run_cubes finished ({len(recs)} records, "
          f"{sum(x['status'] == 'UNKNOWN' for x in recs)} split)")
    want = hashlib.sha256(body.encode()).hexdigest()
    got = (d / "run/body.sha256").read_text().split()[0]
    check(got == want, "body.sha256 = sha256 of the CNF without its header")
    s = summary(cnf, d)
    check(s["verdict"] == "ALL CLOSED" and s["cover"].startswith("VERIFIED") and s["body_sha256"] == want,
          f"cnc_summary: {s['verdict']}, cover {s['cover']}, {s['verified_leaves']} leaves, body_sha256 reported")
    c = closure(d)
    check(c.returncode == 0, f"closure.py: {c.stdout.strip()}")
    n1 = td / "neg1"
    shutil.copytree(d, n1)
    recs = [json.loads(l) for l in (n1 / "run/results.jsonl").read_text().splitlines()]
    leaf0 = next(x for x in recs if "." not in x["id"])
    leaf0["lits"] = [-v for v in leaf0["lits"]]
    (n1 / "run/results.jsonl").write_text("".join(json.dumps(x) + "\n" for x in recs))
    s = summary(cnf, n1)
    c = closure(n1)
    check(s["verdict"] == "NOT CLOSED" and c.returncode != 0,
          f"level-0 record {leaf0['id']} with other literals than its cube: {s['verdict']} {s['problems'][:1]}, closure exit {c.returncode}")
    n2 = td / "neg2"
    shutil.copytree(d, n2)
    with open(n2 / "run/body.cnf", "a") as fh:
        fh.write("1 2 0\n")
    s = summary(cnf, n2)
    check(s["verdict"] == "NOT CLOSED", f"body.cnf changed after the run: {s['verdict']} {s['problems'][:1]}")
finally:
    shutil.rmtree(td, ignore_errors=True)
print("ALL OK" if bad == 0 else f"FAILED ({bad})")
sys.exit(1 if bad else 0)
