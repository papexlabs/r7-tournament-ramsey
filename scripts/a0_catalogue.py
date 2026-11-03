"""A0: complete catalogues of TT_k-free tournaments for small n, two ways.

(1) One-vertex extension: every TT_k-free tournament on n+1 vertices minus a
    vertex is TT_k-free on n vertices, so C_{n+1} = canon(TT_k-free one-vertex
    extensions of C_n).  build/pivenum extend + nauty labelg.
(2) Independent cross-check for n <= GMAX: gentourng (nauty) generates all
    tournaments on n vertices; build/pivenum filter keeps the TT_k-free ones.
For k = 5 the result is compared with the authors' TT5-free catalogue
(refs/directed-ramsey-src/.../TT5-Free, Mat*.txt) by canonical form.
Writes data/tt{k}free/tt{k}free{n}.d6 (canonical, sorted) and results/a0_k{k}.json.

usage: a0_catalogue.py k NMAX [GMAX]
"""
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402

k, nmax = int(sys.argv[1]), int(sys.argv[2])
gmax = int(sys.argv[3]) if len(sys.argv) > 3 else 0
PIV = str(ROOT / "build/pivenum")
out_dir = ROOT / f"data/tt{k}free"
out_dir.mkdir(parents=True, exist_ok=True)


def canon_sorted(raw: str) -> list[str]:
    if not raw.strip():
        return []
    r = subprocess.run(["labelg", "-q"], input=raw, capture_output=True, text=True, check=True)
    return sorted(set(l for l in r.stdout.splitlines() if l.strip()))


res = {"k": k, "counts": {}, "gentourng_counts": {}, "match_gentourng": {}, "match_authors": {}}
t0 = time.time()
cat = canon_sorted(T.to_d6([0]) + "\n")
(out_dir / f"tt{k}free1.d6").write_text("\n".join(cat) + "\n")
res["counts"][1] = len(cat)
for n in range(1, nmax):
    r = subprocess.run(["nice", "-n", "10", PIV, "extend", str(k)], input="\n".join(cat) + "\n",
                       capture_output=True, text=True, check=True)
    cat = canon_sorted(r.stdout)
    (out_dir / f"tt{k}free{n+1}.d6").write_text("\n".join(cat) + ("\n" if cat else ""))
    res["counts"][n + 1] = len(cat)
    print(f"n={n+1}: {len(cat)}  ({time.time()-t0:.1f}s)", flush=True)
    if not cat:
        break

for n in range(1, gmax + 1):
    g = subprocess.Popen(["nice", "-n", "10", "gentourng", "-z", "-q", str(n)], stdout=subprocess.PIPE)
    f = subprocess.run(["nice", "-n", "10", PIV, "filter", str(k)], stdin=g.stdout, capture_output=True, text=True)
    g.wait()
    gc = canon_sorted(f.stdout)
    mine = [l for l in (out_dir / f"tt{k}free{n}.d6").read_text().splitlines() if l]
    res["gentourng_counts"][n] = len(gc)
    res["match_gentourng"][n] = gc == mine
    print(f"gentourng n={n}: {len(gc)} match={gc == mine} ({time.time()-t0:.1f}s)", flush=True)

if k == 5:
    base = ROOT / "refs/directed-ramsey-src/Directed-Ramsey-master/TT5-Free"
    for n in range(1, nmax + 1):
        d = base / f"{n}-Vertex"
        if not d.exists():
            continue
        theirs = canon_sorted("\n".join(T.to_d6(T.matrix_to_out(T.read_matrix(p))) for p in d.glob("Mat*.txt")) + "\n")
        mine = [l for l in (out_dir / f"tt{k}free{n}.d6").read_text().splitlines() if l]
        res["match_authors"][n] = (len(theirs), theirs == mine)
res["seconds"] = round(time.time() - t0, 1)
(ROOT / f"results/a0_k{k}.json").write_text(json.dumps(res, indent=1))
print(json.dumps(res))
