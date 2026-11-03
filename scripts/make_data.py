"""Write data/I24_<L>.txt and data/I23_<L>.txt using the paper's letters.

Sub-ST27 classes come from our own ST27 construction (data/subST27_*.txt from
e1_catalog.py), matched to the published letters by nauty canonical form.
23W/23X (doubly regular, from McKay's catalogue via the authors' repo) are
copied; 23Y is our own QR(23) circulant (isomorphic to the published 23Y).
"""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T
REPO = ROOT / "refs/directed-ramsey-src/Directed-Ramsey-master/TT6-Free"
D = ROOT / "data"
def full(p): return T.matrix_to_out(T.read_matrix(p))
own = {}
for p in sorted(D.glob("subST27_2[34]_*.txt")):
    o = full(p); own[T.canon(o)] = o
for L in "ABCDE":
    c = T.canon(full(REPO / f"24-Vertex/24{L}.txt"))
    T.write_matrix(T.out_to_rows(own[c]), D / f"I24_{L}.txt")
for L in "ABCDEFGHIJKLMNOPQRSTUV":
    c = T.canon(full(REPO / f"23-Vertex/SubST27/23{L}.txt"))
    T.write_matrix(T.out_to_rows(own[c]), D / f"I23_{L}.txt")
for L in "WX":
    o = full(REPO / f"23-Vertex/Doubly-Regular/23{L}.txt")
    T.write_matrix(T.out_to_rows(o), D / f"I23_{L}.txt")
q = T.qr_circulant(23)
assert T.canon(q) == T.canon(full(REPO / "23-Vertex/Doubly-Regular/23Y.txt"))
T.write_matrix(T.out_to_rows(q), D / "I23_Y.txt")
print("ok", len(list(D.glob("I24_*.txt"))), len(list(D.glob("I23_*.txt"))))
