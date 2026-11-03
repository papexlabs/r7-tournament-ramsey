"""Solve MATRIX's CNF with cadical and check a SAT model independently.

usage: verify_model.py MATRIX CNF [k] [units...]
Rebuilds the completed tournament from the model (arc variables are the free
pairs i<j in row-major order, as in build/encode) and checks with tourn.max_tt
that it has no TT_k.  Writes the completed tournament to results/models/.
"""
import subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T
mat, cnf = sys.argv[1], sys.argv[2]
k = int(sys.argv[3]) if len(sys.argv) > 3 else 7
units = [int(x) for x in sys.argv[4:]]
rows = T.read_matrix(mat); n = len(rows)
src = cnf
if units:
    lines = Path(cnf).read_text().splitlines(); h = lines[0].split()
    tf = tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False)
    tf.write(f"p cnf {h[2]} {int(h[3]) + len(units)}\n" + "\n".join(lines[1:]) + "\n" + "".join(f"{u} 0\n" for u in units)); tf.close()
    src = tf.name
r = subprocess.run(["nice", "-n", "10", "cadical", "-q", src], capture_output=True, text=True)
if r.returncode != 10:
    print("status", r.returncode); sys.exit(0)
true = set()
for line in r.stdout.splitlines():
    if line.startswith("v"):
        true.update(int(x) for x in line.split()[1:] if int(x) > 0)
out = [0] * n; var = 0
for i in range(n):
    for j in range(i + 1, n):
        c = rows[i][j]
        if c == "*":
            var += 1
            c = "1" if var in true else "0"
        if c == "1": out[i] |= 1 << j
        else: out[j] |= 1 << i
T.check_tournament(out)
mt = T.max_tt(out)
(ROOT / "results/models").mkdir(parents=True, exist_ok=True)
name = Path(mat).stem
T.write_matrix(T.out_to_rows(out), ROOT / f"results/models/{name}.txt")
print(f"{name}: SAT model, n={n}, largest transitive subtournament = {mt} -> {'TT%d-free OK' % k if mt < k else 'CONTAINS TT%d: BUG' % k}")
