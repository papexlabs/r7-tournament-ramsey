"""Solve MATRIX's CNF with cadical and check a SAT model independently.

usage: verify_model.py MATRIX CNF [k] [units...]
       verify_model.py --model MODEL [--numbering nmh|free] [--out DIR] MATRIX CNF [k]
Rebuilds the completed tournament from the model and checks with tourn.max_tt
that it has no TT_k.  Writes the completed tournament to results/models/.

--numbering free (default): arc variables are the free pairs i<j in row-major
  order, as in build/encode.
--numbering nmh: NMH's encoding/tour-encode.c numbering: the pair a<b
  (1-based) is variable a + (b-2)(b-1)/2, true iff a->b; the fixed arcs are
  unit clauses and are checked against MATRIX.
--model MODEL: do not re-solve; check the saved model (whitespace-separated
  literals, e.g. run_cubes.py's SAT_<id>.model).  Every clause of CNF must be
  satisfied by it (checked here, independently of the solver).
--out DIR: where the completed tournament goes (default results/models).
Exit status 1 if the model is not a model, contradicts MATRIX or contains TT_k.
"""
import subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T
args = sys.argv[1:]
numbering, model_path, outdir = "free", None, ROOT / "results/models"
while args and args[0].startswith("--"):
    opt = args.pop(0)
    if opt == "--numbering":
        numbering = args.pop(0)
    elif opt == "--model":
        model_path = args.pop(0)
    elif opt == "--out":
        outdir = Path(args.pop(0))
    else:
        sys.exit(f"unknown option {opt}")
mat, cnf = args[0], args[1]
k = int(args[2]) if len(args) > 2 else 7
units = [int(x) for x in args[3:]]
rows = T.read_matrix(mat); n = len(rows)
if model_path:
    true = set()
    for x in Path(model_path).read_text().split():
        if int(x) > 0:
            true.add(int(x))
    unsat_cls = 0
    with open(cnf) as fh:
        for line in fh:
            if not line.strip() or line[0] in "pc":
                continue
            lits = [int(x) for x in line.split()[:-1]]
            if not any((l > 0) == (abs(l) in true) for l in lits):
                unsat_cls += 1
    if unsat_cls:
        print(f"model violates {unsat_cls} clauses of {cnf}: NOT A MODEL"); sys.exit(1)
    print(f"model satisfies every clause of {cnf}")
else:
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
        if numbering == "nmh":
            v = (i + 1) + (j - 1) * j // 2
            got = "1" if v in true else "0"
            if c != "*" and c != got:
                print(f"model contradicts the fixed arc ({i},{j}) of {mat}: BUG"); sys.exit(1)
            c = got
        elif c == "*":
            var += 1
            c = "1" if var in true else "0"
        if c == "1": out[i] |= 1 << j
        else: out[j] |= 1 << i
T.check_tournament(out)
mt = T.max_tt(out)
outdir.mkdir(parents=True, exist_ok=True)
name = Path(mat).stem
T.write_matrix(T.out_to_rows(out), outdir / f"{name}.txt")
print(f"{name}: SAT model, n={n}, largest transitive subtournament = {mt} -> {'TT%d-free OK' % k if mt < k else 'CONTAINS TT%d: BUG' % k}")
sys.exit(0 if mt < k else 1)
