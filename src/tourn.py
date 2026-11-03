"""Tournament utilities for the R(7) <= 46 feasibility study.

Conventions
-----------
A tournament on n vertices is a list of n Python ints ``out`` where bit j of
``out[i]`` is set iff i -> j.  A *partial* tournament (instance input) is an
n x n matrix of characters '0', '1', '*' read row-wise; only the upper
triangle (j > i) is authoritative, as in the Neiman-Mackey-Heule files
('1' at (i, j) means i -> j, '0' means j -> i, '*' means free).
"""

from __future__ import annotations

import itertools
import subprocess
from pathlib import Path

# ----------------------------------------------------------------------------
# basic I/O


def read_matrix(path: str | Path) -> list[list[str]]:
    rows = []
    for line in Path(path).read_text().splitlines():
        toks = line.split()
        if toks:
            rows.append(toks)
    n = len(rows)
    for r in rows:
        if len(r) != n:
            raise ValueError(f"{path}: row length {len(r)} != {n}")
    return rows


def matrix_to_out(rows: list[list[str]]) -> list[int]:
    """Full (no '*') matrix -> out-bitsets, using the upper triangle."""
    n = len(rows)
    out = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            c = rows[i][j]
            if c == "1":
                out[i] |= 1 << j
            elif c == "0":
                out[j] |= 1 << i
            else:
                raise ValueError("free arc in full tournament")
    return out


def out_to_rows(out: list[int]) -> list[list[str]]:
    n = len(out)
    return [["1" if (out[i] >> j) & 1 else "0" for j in range(n)] for i in range(n)]


def write_matrix(rows: list[list[str]], path: str | Path) -> None:
    Path(path).write_text("\n".join(" ".join(r) for r in rows) + "\n")


def check_tournament(out: list[int]) -> None:
    n = len(out)
    for i in range(n):
        if (out[i] >> i) & 1:
            raise ValueError("loop")
        for j in range(i + 1, n):
            a, b = (out[i] >> j) & 1, (out[j] >> i) & 1
            if a + b != 1:
                raise ValueError(f"pair {i},{j} not a tournament arc")


def induced(out: list[int], verts: list[int]) -> list[int]:
    idx = {v: t for t, v in enumerate(verts)}
    res = []
    for v in verts:
        m = 0
        for w in verts:
            if (out[v] >> w) & 1:
                m |= 1 << idx[w]
        res.append(m)
    return res


def reverse(out: list[int]) -> list[int]:
    n = len(out)
    full = (1 << n) - 1
    return [(~out[i]) & full & ~(1 << i) for i in range(n)]


def outdegrees(out: list[int]) -> list[int]:
    return [bin(x).count("1") for x in out]


# ----------------------------------------------------------------------------
# transitive subtournaments


def max_tt(out: list[int]) -> int:
    """Order of the largest transitive subtournament (exact, branch & bound)."""
    n = len(out)
    best = 0

    def rec(cand: int, depth: int) -> None:
        nonlocal best
        if depth > best:
            best = depth
        if cand == 0:
            return
        # trivial bound: depth + |cand|
        if depth + bin(cand).count("1") <= best:
            return
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            rec(cand & out[v], depth + 1)

    rec((1 << n) - 1, 0)
    return best


def has_tt(out: list[int], k: int) -> bool:
    n = len(out)

    def rec(cand: int, need: int) -> bool:
        if need == 0:
            return True
        if bin(cand).count("1") < need:
            return False
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            if rec(cand & out[v], need - 1):
                return True
        return False

    return rec((1 << n) - 1, k)


def count_tt(out: list[int], k: int) -> int:
    """Number of k-vertex subsets inducing a transitive tournament."""
    n = len(out)
    # a transitive k-set has a unique source; count chains source-first
    def rec(cand: int, need: int) -> int:
        if need == 0:
            return 1
        tot = 0
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            tot += rec(cand & out[v], need - 1)
        return tot

    return rec((1 << n) - 1, k)


def three_cycles(out: list[int]) -> int:
    n = len(out)
    d = outdegrees(out)
    return n * (n - 1) * (n - 2) // 6 - sum(x * (x - 1) // 2 for x in d)


# ----------------------------------------------------------------------------
# ST27 = quadratic-residue (Paley) tournament on GF(27)


def gf27_elements():
    return list(itertools.product(range(3), repeat=3))  # (a0, a1, a2)


def gf27_mul(a, b):
    # polynomials over GF(3) modulo x^3 - x - 1  (x^3 = x + 1)
    prod = [0] * 5
    for i in range(3):
        for j in range(3):
            prod[i + j] = (prod[i + j] + a[i] * b[j]) % 3
    for d in (4, 3):
        c = prod[d]
        if c:
            prod[d] = 0
            prod[d - 3] = (prod[d - 3] + c) % 3  # x^d = x^(d-3) * (x + 1)
            prod[d - 2] = (prod[d - 2] + c) % 3
    return tuple(prod[:3])


def gf27_sub(a, b):
    return tuple((x - y) % 3 for x, y in zip(a, b))


def st27() -> list[int]:
    els = gf27_elements()
    zero = (0, 0, 0)
    squares = {gf27_mul(a, a) for a in els if a != zero}
    assert len(squares) == 13
    # -1 must be a non-square (27 = 3 mod 4)
    assert (2, 0, 0) not in squares
    out = [0] * 27
    for i, a in enumerate(els):
        for j, b in enumerate(els):
            if i != j and gf27_sub(b, a) in squares:
                out[i] |= 1 << j
    check_tournament(out)
    return out


def qr_circulant(p: int) -> list[int]:
    qr = {(x * x) % p for x in range(1, p)}
    out = [0] * p
    for i in range(p):
        for j in range(p):
            if i != j and (j - i) % p in qr:
                out[i] |= 1 << j
    check_tournament(out)
    return out


# ----------------------------------------------------------------------------
# canonical forms via nauty (labelg, digraph6)


def to_d6(out: list[int]) -> str:
    n = len(out)
    assert n < 63
    bits = []
    for i in range(n):
        for j in range(n):
            bits.append((out[i] >> j) & 1)
    while len(bits) % 6:
        bits.append(0)
    s = "&" + chr(n + 63)
    for t in range(0, len(bits), 6):
        v = 0
        for b in bits[t : t + 6]:
            v = (v << 1) | b
        s += chr(v + 63)
    return s


def from_d6(s: str) -> list[int]:
    s = s.strip()
    assert s[0] == "&"
    n = ord(s[1]) - 63
    bits = []
    for ch in s[2:]:
        v = ord(ch) - 63
        for t in range(5, -1, -1):
            bits.append((v >> t) & 1)
    out = [0] * n
    for i in range(n):
        for j in range(n):
            if bits[i * n + j]:
                out[i] |= 1 << j
    return out


def canon_many(outs: list[list[int]]) -> list[str]:
    """Canonical digraph6 strings (nauty labelg) for a batch of tournaments."""
    if not outs:
        return []
    inp = "\n".join(to_d6(o) for o in outs) + "\n"
    res = subprocess.run(
        ["labelg", "-q"], input=inp, capture_output=True, text=True, check=True
    )
    lines = [l for l in res.stdout.splitlines() if l.strip()]
    assert len(lines) == len(outs)
    return lines


def canon(out: list[int]) -> str:
    return canon_many([out])[0]


# ----------------------------------------------------------------------------
# subtournament containment (induced, labelled embedding search)


def find_embedding(small: list[int], big: list[int], first_only: bool = True):
    """Count (or find) injective maps f with small[i]->small[j] iff f(i)->f(j).

    Returns the number of embeddings (labelled), or the first one if
    first_only.  Vertex order of ``small`` is chosen greedily for pruning.
    """
    m, n = len(small), len(big)
    order = sorted(range(m), key=lambda v: -bin(small[v]).count("1"))
    full = (1 << n) - 1
    big_in = [0] * n
    for i in range(n):
        for j in range(n):
            if (big[i] >> j) & 1:
                big_in[j] |= 1 << i
    count = 0
    image = [0] * m

    def rec(t: int, used: int, placed: list[int]):
        nonlocal count
        if t == m:
            count += 1
            return first_only
        v = order[t]
        cand = full & ~used
        for u in placed:
            w = image[u]
            if (small[u] >> v) & 1:  # u -> v, so f(u) -> f(v)
                cand &= big[w]
            else:
                cand &= big_in[w]
        while cand:
            x = (cand & -cand).bit_length() - 1
            cand &= cand - 1
            image[v] = x
            if rec(t + 1, used | (1 << x), placed + [v]):
                return True
        return False

    found = rec(0, 0, [])
    if first_only:
        return [image[i] for i in range(m)] if found else None
    return count


def contains(big: list[int], small: list[int]) -> bool:
    return find_embedding(small, big, True) is not None
