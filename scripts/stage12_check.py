"""After Stages 1-2 (on the Mac, after sync): go/no-go 1 and 2.

For n = 25, 24, 23, 22, 21 (whatever results/enum/k6n{n} exists):
 - the enumeration is complete (all jobs status complete) and certified
   (every job LRAT VERIFIED);
 - its classes (re-canonicalised here with labelg) equal the Lohn file
   tt6free{n}.d6 and, for n = 23..25, NMH's classes;
 - S22: every class on 22 vertices contains Y8;
 - S21: every class on 21 vertices contains Y8 except exactly O21*.
Writes results/stage12_check.json and prints GO / NO-GO lines.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402

LOHN = ROOT / "refs/digraph-isolators-src/digraph_isolators-HEAD/tt6free_tournaments"
Y8 = T.matrix_to_out(T.read_matrix(ROOT / "data/Y8.txt"))
O21 = T.matrix_to_out(T.read_matrix(ROOT / "data/O21star.txt"))
res = {}
for n in (25, 24, 23, 22, 21):
    d = ROOT / f"results/enum/k6n{n}"
    if not (d / "summary.json").exists():
        continue
    s = json.loads((d / "summary.json").read_text())
    c = json.loads((d / "certify_summary.json").read_text()) if (d / "certify_summary.json").exists() else {}
    ours = [T.from_d6(l) for l in (d / "classes.d6").read_text().split()]
    can = set(T.canon_many(ours)) if ours else set()
    r = {"jobs": s["jobs_total"], "enum_complete": s["all_complete"], "certified": c.get("all_jobs_verified", False),
         "classes": len(can)}
    lohn = [T.from_d6(l) for l in (LOHN / f"tt6free{n}.d6").read_text().split()] if LOHN.exists() else []
    if lohn:
        lc = set(T.canon_many(lohn))
        r["equals_lohn"] = lc == can
        r["missing_from_lohn"] = len(can - lc)
        r["missing_from_ours"] = len(lc - can)
    if n in (23, 24):
        nmh = set(T.canon_many([T.matrix_to_out(T.read_matrix(p)) for p in sorted((ROOT / "data").glob(f"I{n}_*.txt"))]))
        r["equals_nmh"] = nmh == can
    if n == 25:
        st = T.matrix_to_out(T.read_matrix(ROOT / "data/ST27.txt"))
        r["equals_nmh"] = can == {T.canon(T.induced(st, list(range(25))))}
    if n in (21, 22):
        noy = [o for o in ours if not T.contains(o, Y8)]
        r["without_Y8"] = len(noy)
        if n == 21:
            r["without_Y8_is_exactly_O21star"] = len(noy) == 1 and T.canon(noy[0]) == T.canon(O21)
    res[n] = r
    print(n, json.dumps(r), flush=True)
(ROOT / "results/stage12_check.json").write_text(json.dumps(res, indent=1))
ok = lambda n: n in res and res[n]["enum_complete"] and res[n]["certified"]
if 22 in res:
    g1 = ok(22) and res[22]["without_Y8"] == 0 and all(res[m].get("equals_nmh", False) for m in (23, 24, 25) if m in res)
    print("GO/NO-GO 1:", "GO ((23,22) closed modulo NMH's Y8 runs)" if g1 else "NO-GO (see results/stage12_check.json)")
if 21 in res:
    g2 = ok(21) and res[21].get("without_Y8_is_exactly_O21star", False)
    print("GO/NO-GO 2:", "GO (Stage 3 = the five instances I24X -p- O21*)" if g2 else "NO-GO (see results/stage12_check.json)")
