#!/usr/bin/env python3
"""Generate the data of the CNF milestone (run from r7lean/ with `python3 -I tools/gen_enc_data.py`).

Writes
  R7lean/Enc/Instances.lean  (core only, no Mathlib): raw row bitmasks of every tournament used
      by the 33 pivot instances, the instances as `PivotSpec`s, and for each one its name,
      encoder, DIMACS header variable count and the sha256 / clause / byte counts of
      data/stage4_manifest.json and data/stage3_manifest.json;
  R7lean/NMHIso.lean  (Mathlib): for each NMH input whose X block is not literally one of our
      tournaments, an explicit isomorphism (a permutation found here by backtracking) onto
      ST25 or I23X; the isomorphism property is checked in Lean by `decide`.

Conventions as in tools/gen_data.py: entry (i, j) of a matrix is 1 iff i -> j, row i is the
bitmask sum_j M[i][j] 2^j, and the Lean side (`upperArc`, `ofRows`) reads the upper triangle.
For NMH's inputs ('*' = free pair) this script checks that the file is the pivot instance
X -> p -> Z with exactly the X x Z pairs free, that both triangles agree, and that the Z block
equals our Y8 / H6 / W7; the X block is taken from the file.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]          # r7lean/
ROOT = HERE.parent
DATA = ROOT / "data"
NMH = ROOT / "refs/directed-ramsey-src/Directed-Ramsey-master"
L23 = "ABCDEFGHIJKLMNOPQRSTUVWXY"
L24 = "ABCDE"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_cells(path):
    rows = [l.split() for l in path.read_text().splitlines() if l.split()]
    n = len(rows)
    assert all(len(r) == n for r in rows), path
    return rows


def read_tour(path):
    rows = read_cells(path)
    n = len(rows)
    for i in range(n):
        for j in range(n):
            c = rows[i][j]
            assert c in "01", (path, i, j, c)
            if i == j:
                assert c == "0"
            elif i < j:
                assert (c == "1") != (rows[j][i] == "1"), (path, i, j)
    return [sum(1 << j for j, c in enumerate(r) if c == "1") for r in rows]


def beats(masks, i, j):
    return (masks[i] >> j) & 1 == 1


def sub(masks, vs):
    return [sum(1 << jj for jj, v in enumerate(vs) if u != v and beats(masks, u, v)) for u in vs]


def pivot_blocks(path, b):
    """Check that `path` is the pivot instance X -> p -> Z (|Z| = b) and return the masks of X, Z."""
    rows = read_cells(path)
    n = len(rows)
    a = n - 1 - b
    X, Z = range(a), range(a + 1, n)
    for i in range(n):
        for j in range(n):
            c = rows[i][j]
            if i == j:
                continue
            cross = (i in X and j in Z) or (i in Z and j in X)
            if cross:
                assert c == "*", (path, i, j)
                continue
            assert c in "01", (path, i, j, c)
            assert (c == "1") != (rows[j][i] == "1"), (path, i, j)
            if j == a and i in X:
                assert c == "1"
            if i == a and j in Z:
                assert c == "1"
    xm = [sum(1 << j for j in X if j != i and rows[i][j] == "1") for i in X]
    zm = [sum(1 << (j - a - 1) for j in Z if j != i and rows[i][j] == "1") for i in Z]
    return a, xm, zm


def iso(A, B):
    """A permutation s with A: i -> j iff B: s[i] -> s[j], by backtracking."""
    n = len(A)
    assert len(B) == n

    def inv(M):
        out = [bin(m).count("1") for m in M]
        return [(out[v], tuple(sorted(out[u] for u in range(n) if beats(M, v, u))),
                 tuple(sorted(out[u] for u in range(n) if beats(M, u, v)))) for v in range(n)]
    ia, ib = inv(A), inv(B)
    assert sorted(ia) == sorted(ib), "invariants differ"
    order = []
    rest = set(range(n))
    while rest:  # greedy: next the vertex with the rarest invariant
        v = min(rest, key=lambda x: (sum(1 for y in ib if y == ia[x]), x))
        order.append(v)
        rest.remove(v)
    s = [-1] * n
    used = [False] * n

    def bt(d):
        if d == n:
            return True
        v = order[d]
        for w in range(n):
            if used[w] or ib[w] != ia[v]:
                continue
            if all(beats(A, v, u) == beats(B, w, s[u]) for u in order[:d]):
                s[v] = w
                used[w] = True
                if bt(d + 1):
                    return True
                used[w] = False
        s[v] = -1
        return False
    assert bt(0), "not isomorphic"
    for i in range(n):
        for j in range(n):
            if i != j:
                assert beats(A, i, j) == beats(B, s[i], s[j])
    return s


def vec(masks, first, indent="    "):
    lines, cur = [], first + "["
    for k, m in enumerate(masks):
        tok = str(m) + ("]" if k == len(masks) - 1 else ",")
        if len(cur) + 1 + len(tok) > 100:
            lines.append(cur)
            cur = indent + tok
        else:
            cur += tok if cur.endswith("[") else " " + tok
    lines.append(cur)
    return "\n".join(lines)


# ---------------------------------------------------------------- our tournaments
ours = {}
for name, file in [("ST27", "ST27.txt"), ("H6", "H6.txt"), ("W7", "W7.txt"), ("Y8", "Y8.txt"),
                   ("O21s", "O21star.txt")] + [(f"I24{L}", f"I24_{L}.txt") for L in L24] + \
                  [(f"I23{L}", f"I23_{L}.txt") for L in L23]:
    ours[name] = (read_tour(DATA / file), sha(DATA / file), f"data/{file}")
TT5 = [sum(1 << j for j in range(i + 1, 5)) for i in range(5)]
ST25 = sub(ours["ST27"][0], list(range(2, 27)))
ST26 = sub(ours["ST27"][0], list(range(1, 27)))

# ---------------------------------------------------------------- inputs and manifests
m4 = json.loads((DATA / "stage4_manifest.json").read_text())["instances"]
m3 = json.loads((DATA / "stage3_manifest.json").read_text())["instances"]

# ST26-p-TT5: our own input; check it is exactly pivot(ST26, TT5)
a, xm, zm = pivot_blocks(DATA / "ST26-p-TT5.txt", 5)
assert a == 26 and xm == ST26 and zm == TT5
assert sha(DATA / "ST26-p-TT5.txt") == m4["ST26-p-TT5"]["input_sha256"]

nmh = {}   # name -> (X masks, input path, input sha, Z name)
for name, path, zname, b in [("ST25-p-H6", NMH / "log25/ST25-p-H6.txt", "H6", 6),
                             ("ST25-p-W7", NMH / "log25/ST25-p-W7.txt", "W7", 7)] + \
                            [(f"23{L}-p-Y8", NMH / f"log23/23{L}-p-Y8.txt", "Y8", 8) for L in L23]:
    a, xm, zm = pivot_blocks(path, b)
    assert zm == ours[zname][0], f"{name}: Z block differs from data/{zname}"
    h = sha(path)
    assert h == m4[name]["input_sha256"], name
    nmh[name] = (xm, path.relative_to(ROOT), h, zname)

isos = {}
for name, (xm, _, _, _) in nmh.items():
    ref = ST25 if name.startswith("ST25") else ours[f"I23{name[2]}"][0]
    isos[name] = iso(xm, ref)

# ---------------------------------------------------------------- Instances.lean
out = []
w = out.append
w("import R7lean.Enc.Basic")
w("")
w("/-!")
w("# The 33 pivot instances (generated)")
w("")
w("GENERATED by `tools/gen_enc_data.py`; do not edit by hand. No Mathlib.")
w("")
w("Raw row bitmasks (row `i` = `∑ⱼ M[i][j] 2^j`, read through `upperArc`, as `Tournament.ofRows`")
w("reads them) of the tournaments of `R7lean/Data.lean` that occur in the instances, and of the `X`")
w("blocks of NMH's 27 input files. For NMH's inputs the generator checked that the file is the")
w("pivot instance `X → p → Z` with exactly the `X × Z` pairs free (both triangles), and that its")
w("`Z` block equals our `Y8` / `H6` / `W7`. `data/ST26-p-TT5.txt` is exactly `ST26 -p- TT5`, and")
w("the Stage 3 matrices are built from `data/I24_X.txt` and `data/O21star.txt` (`src/instances.py`).")
w("")
w("`entries` lists the instances with the encoder, the header variable count and the sha256, clause")
w("count and byte count of the CNF from `data/stage4_manifest.json` / `data/stage3_manifest.json`.")
w("-/")
w("")
w("namespace R7.Enc.Inst")
w("")
for name in ["ST27", "H6", "W7", "Y8", "O21s"] + [f"I24{L}" for L in L24]:
    masks, h, file = ours[name]
    w(f"/-- `{name}`, from `{file}` (sha256 `{h}`). -/")
    w(vec(masks, f"def rows{name} : List Nat :=\n  "))
    w("")
w("/-- `TT₅` (`i → j` iff `i < j`). -/")
w(vec(TT5, "def rowsTT5 : List Nat :=\n  "))
w("")
for name, (xm, path, h, _) in nmh.items():
    ident = "rowsNMH" + name.replace("-p-", "_").replace("-", "_")
    w(f"/-- The `X` block of NMH's input `{path}` (sha256 `{h}`). -/")
    w(vec(xm, f"def {ident} : List Nat :=\n  "))
    w("")
w("/-- The `X` blocks of NMH's inputs `23X-p-Y8`, `X = A, …, Y`. -/")
w("def rowsNMH23 : List (List Nat) :=")
w("  [" + ", ".join(f"rowsNMH23{L}_Y8" for L in L23[:8]) + ",")
w("    " + ", ".join(f"rowsNMH23{L}_Y8" for L in L23[8:16]) + ",")
w("    " + ", ".join(f"rowsNMH23{L}_Y8" for L in L23[16:]) + "]")
w("")
w("/-- `I24A, …, I24E`. -/")
w("def rowsI24 : List (List Nat) :=")
w("  [" + ", ".join(f"rowsI24{L}" for L in L24) + "]")
w("")
w("/-- `ST26 -p- TT5`; `ST26` is `ST27` minus vertex `0`. -/")
w("def specST26_TT5 : PivotSpec :=")
w("  ⟨26, 5, fun i j => upperArc rowsST27 (i + 1) (j + 1), upperArc rowsTT5⟩")
w("")
w("/-- NMH's `ST25-p-H6`. -/")
w("def specST25_H6 : PivotSpec := ⟨25, 6, upperArc rowsNMHST25_H6, upperArc rowsH6⟩")
w("")
w("/-- NMH's `ST25-p-W7`. -/")
w("def specST25_W7 : PivotSpec := ⟨25, 7, upperArc rowsNMHST25_W7, upperArc rowsW7⟩")
w("")
w("/-- NMH's `23X-p-Y8` (`i = 0` is `A`, …, `i = 24` is `Y`). -/")
w("def spec23_Y8 (i : Nat) : PivotSpec := ⟨23, 8, upperArc (rowsNMH23.getD i []), upperArc rowsY8⟩")
w("")
w("/-- `24X -p- O21s` (`i = 0` is `A`, …, `i = 4` is `E`). -/")
w("def spec24_O21s (i : Nat) : PivotSpec := ⟨24, 21, upperArc (rowsI24.getD i []), upperArc rowsO21s⟩")
w("")
w("/-- The encoder of an instance. -/")
w("inductive Encoder where")
w("  /-- NMH's `tour-encode.c` (`R7lean/Enc/NMH.lean`) -/")
w("  | nmh")
w("  /-- `src/encode.c`, 3-cycle mode, `k = 7`, `limit = 1` (`R7lean/Enc/Tri.lean`) -/")
w("  | tri")
w("  deriving BEq, Repr")
w("")
w("structure Entry where")
w("  name : String")
w("  enc : Encoder")
w("  spec : PivotSpec")
w("  /-- the header variable count, for NMH's encoder (fixed by `scripts/stage4_instances.py`);")
w("  for `src/encode.c` it is the number of variables used -/")
w("  headerVars : Option Nat")
w("  sha256 : String")
w("  clauses : Nat")
w("  bytes : Nat")
w("")
w("/-- The 33 instances and their manifest entries. -/")
w("def entries : List Entry := [")
ents = []
for name in ["ST26-p-TT5", "ST25-p-H6", "ST25-p-W7"] + [f"23{L}-p-Y8" for L in L23]:
    e = m4[name]
    spec = ({"ST26-p-TT5": "specST26_TT5", "ST25-p-H6": "specST25_H6", "ST25-p-W7": "specST25_W7"}[name]
            if name.startswith("ST") else f"spec23_Y8 {L23.index(name[2])}")
    ents.append(f'  ⟨"{name}", .nmh, {spec}, some {e["vars"]},\n    "{e["cnf_sha256"]}", {e["clauses"]}, {e["bytes"]}⟩')
for L in L24:
    name = f"24{L}-p-O21s"
    e = m3[name]
    ents.append(f'  ⟨"{name}", .tri, spec24_O21s {L24.index(L)}, none,\n    "{e["cnf_sha256"]}", {e["clauses"]}, {e["bytes"]}⟩')
w(",\n".join(ents) + "]")
w("")
w("end R7.Enc.Inst")
(HERE / "R7lean/Enc/Instances.lean").write_text("\n".join(out) + "\n")

# ---------------------------------------------------------------- NMHIso.lean
out = []
w = out.append
w("import R7lean.Data")
w("import R7lean.EncSound")
w("import R7lean.Enc.Instances")
w("")
w("/-!")
w("# NMH's labelled `X` blocks are isomorphic to our tournaments (generated)")
w("")
w("GENERATED by `tools/gen_enc_data.py`; do not edit by hand.")
w("")
w("For each NMH input, `nmh…` is the tournament of its `X` block (`ofRows` of the raw rows of")
w("`R7lean/Enc/Instances.lean`), and `perm…` an explicit vertex permutation, found by the generator")
w("by backtracking, onto `ST25` (for `ST25-p-H6`, `ST25-p-W7`) or onto `I23X` (for `23X-p-Y8`).")
w("That it is an isomorphism is checked by `decide` (`isoOfPerm`), in the kernel; this replaces the")
w("canonical-form comparison of `scripts/stage4_instances.py` (`X_iso_reference`).")
w("-/")
w("")
w("namespace R7")
w("")
w("open Tournament Enc Enc.Inst")
w("")
for name, (xm, path, h, _) in nmh.items():
    s = isos[name]
    ident = name.replace("-p-", "_").replace("-", "_")
    rows = "rowsNMH" + ident
    n = len(xm)
    ref = "ST25" if name.startswith("ST25") else f"I23{name[2]}"
    inv = [0] * n
    for i, x in enumerate(s):
        inv[x] = i
    w(f"/-- The `X` block of NMH's `{name}`, from")
    w(f"`{path}`. -/")
    w(f"def nmh{ident} : Tournament (Fin {n}) := ofRows {rows}")
    w("")
    w(f"/-- An isomorphism `nmh{ident} ≅ {ref}` (vertex `i` ↦ `perm[i]`). -/")
    w(vec(s, f"def perm{ident} : List Nat :=\n  "))
    w("")
    w(vec(inv, f"def permInv{ident} : List Nat :=\n  "))
    w("")
    w(f"theorem iso{ident}_ok : IsoOfPerm {rows} perm{ident} permInv{ident} {ref} := by")
    w("  decide +kernel")
    w("")
    w(f"/-- `nmh{ident} ≅ {ref}`. -/")
    w(f"def iso{ident} : nmh{ident}.beats ≃r {ref}.beats :=")
    w(f"  isoOfPerm iso{ident}_ok")
    w("")
w("/-- The `X` block of NMH's `23X-p-Y8` is isomorphic to `I23 i` (`i = 0` is `A`, …). -/")
w("theorem nmh23_iso (i : Fin 25) :")
w("    Nonempty ((ofRows (n := 23) (rowsNMH23.getD i [])).beats ≃r (I23 i).beats) := by")
w("  fin_cases i")
w("  exacts [" + ", ".join(f"⟨iso23{L}_Y8⟩" for L in L23[:7]) + ",")
w("    " + ", ".join(f"⟨iso23{L}_Y8⟩" for L in L23[7:14]) + ",")
w("    " + ", ".join(f"⟨iso23{L}_Y8⟩" for L in L23[14:21]) + ",")
w("    " + ", ".join(f"⟨iso23{L}_Y8⟩" for L in L23[21:]) + "]")
w("")
w("end R7")
(HERE / "R7lean/NMHIso.lean").write_text("\n".join(out) + "\n")
print("wrote R7lean/Enc/Instances.lean, R7lean/NMHIso.lean")
print("identity isomorphisms:", [k for k, v in isos.items() if v == list(range(len(v)))])
