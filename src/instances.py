"""Build partial-tournament matrices for pivot instances.

pivot instance  X -p- Z : vertices = X (fixed, |X| = a), pivot p, Z (fixed, |Z| = b);
X -> p -> Z ; arcs inside X and inside Z fixed; all X x Z arcs free ('*').
A TT_7-free completion exists iff some tournament with a vertex whose
in-neighbourhood is X and whose out-neighbourhood contains Z is TT_7-free
on these a + 1 + b vertices.

free-out instance  X -p- (m free) : like above but Z is m vertices with all
arcs free (inside Z and X x Z).
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tourn as T  # noqa: E402


def pivot_matrix(X: list[int] | None, Z: list[int] | None, a: int | None = None, b: int | None = None):
    a = len(X) if X is not None else a
    b = len(Z) if Z is not None else b
    n = a + 1 + b
    p = a
    rows = [["*"] * n for _ in range(n)]
    for i in range(n):
        rows[i][i] = "0"
    def setarc(u, v):  # u -> v
        rows[u][v] = "1"
        rows[v][u] = "0"
    if X is not None:
        for i in range(a):
            for j in range(a):
                if i != j and (X[i] >> j) & 1:
                    setarc(i, j)
    for i in range(a):
        setarc(i, p)
    for j in range(b):
        setarc(p, a + 1 + j)
    if Z is not None:
        for i in range(b):
            for j in range(b):
                if i != j and (Z[i] >> j) & 1:
                    setarc(a + 1 + i, a + 1 + j)
    return rows


def load(path: str) -> list[int]:
    return T.matrix_to_out(T.read_matrix(path))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("X", help="in-neighbourhood matrix file")
    ap.add_argument("Z", help="out-structure matrix file, or 'free:<m>'")
    ap.add_argument("out")
    a = ap.parse_args()
    X = load(a.X)
    if a.Z.startswith("free:"):
        rows = pivot_matrix(X, None, b=int(a.Z.split(":")[1]))
    else:
        rows = pivot_matrix(X, load(a.Z))
    T.write_matrix(rows, a.out)


if __name__ == "__main__":
    main()
