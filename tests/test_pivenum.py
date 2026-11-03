"""Cross-checks for build/pivenum.

1. dumpcnf (no degree constraints) produces exactly the clause set of
   build/encode on the same pivot matrix (same variable numbering).
2. End-to-end: pivot enumeration of TT5-free tournaments on n = 10..13
   reproduces the complete catalogue counts 369, 45, 1, 1 (scripts/a0_catalogue.py).
Run: python3 tests/test_pivenum.py
"""
import random, subprocess, sys, tempfile, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T, instances as I

def clauses(text):
    out = []
    for line in text.splitlines():
        if not line or line[0] in "pc": continue
        out.append(tuple(sorted(int(x) for x in line.split()[:-1])))
    return sorted(out)

rng = random.Random(5)
bad = 0
for trial in range(6):
    k, (a, b) = rng.choice([(6, (10, 11)), (6, (9, 12)), (5, (5, 6)), (5, (4, 7))])
    ca = ROOT / f"data/tt{k-1}free/tt{k-1}free{a}.d6"; cb = ROOT / f"data/tt{k-1}free/tt{k-1}free{b}.d6"
    LA = ca.read_text().split(); LB = cb.read_text().split()
    ia, ib = rng.randrange(len(LA)), rng.randrange(len(LB))
    d = subprocess.run([str(ROOT / "build/pivenum"), "dumpcnf", str(k), str(ca), str(cb), str(ia), str(ib)],
                       capture_output=True, text=True, check=True).stdout
    with tempfile.TemporaryDirectory() as td:
        mp = Path(td) / "m.txt"; cn = Path(td) / "x.cnf"
        T.write_matrix(I.pivot_matrix(T.from_d6(LA[ia]), T.from_d6(LB[ib])), mp)
        subprocess.run([str(ROOT / "build/encode"), str(mp), str(k), "5900", str(cn)], check=True, capture_output=True)
        e = cn.read_text()
    same = clauses(d) == clauses(e)
    bad += not same
    print(f"dumpcnf vs encode k={k} ({a},{b}) ia={ia} ib={ib}: {'same' if same else 'DIFFERENT'} ({len(clauses(d))} clauses)")
for n, expect in ((10, 369), (11, 45), (12, 1), (13, 1)):
    with tempfile.TemporaryDirectory() as td:
        r = subprocess.run([sys.executable, str(ROOT / "scripts/pivot_enum.py"), "5", str(n), td, "--workers", "2", "--batch", "4"],
                           capture_output=True, text=True, check=True)
        s = json.loads((Path(td) / "summary.json").read_text())
        mine = (ROOT / f"data/tt5free/tt5free{n}.d6").read_text().split()
        cls = (Path(td) / "classes.d6").read_text().split()
        ok = s["all_complete"] and s["classes"] == expect and cls == mine
        bad += not ok
        print(f"pivot enumeration TT5-free n={n}: jobs={s['jobs_total']} classes={s['classes']} expect={expect} identical={cls == mine}")
print("FAIL" if bad else "ALL OK")
sys.exit(1 if bad else 0)
