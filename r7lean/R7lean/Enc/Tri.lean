import R7lean.Enc.Basic

/-!
# The encoder `src/encode.c` (Stage 3), reproduced in Lean (no Mathlib)

`src/encode.c` (sha256 `193796a7…`, `data/stage3_manifest.json`), run as
`build/encode <instance.txt> 7 1 <out.cnf>`, i.e. `k = 7`, `limit = 1`. With `limit = 1` the
Quine–McCluskey step of the C program only ever sees one point, so it is not reproduced; this
file implements exactly the `limit = 1` behaviour:

* variables `1..F`: the free pairs `i < j` in row-major order (true iff `i → j`); 3-cycle
  variables `F+1, …` are created on first use, in that order, and each creation emits its six
  definition clauses `¬t ∨ ¬(x→y) ∨ (y→z)` at that point;
* the `7`-sets are enumerated in lexicographic order, pruning a prefix as soon as it contains
  a fixed 3-cycle (`comb_rec`, `closes_fixed_cycle`);
* per `7`-set `S`: the orderings of `S` compatible with the fixed arcs are counted up to `2`
  (`ext_rec`); none: no clause; exactly one: the clause forbidding it (one literal per free
  pair of `S`, pairs in row-major order); two or more: the clause "some triple of `S` is a
  3-cycle" (`cyc_lit` of each triple: fixed-acyclic triples dropped, triples with one free
  pair replaced by the arc that closes the cycle, others by their 3-cycle variable);
* clauses are built as in `cls_add`/`cls_end`: constant literals are dropped or satisfy the
  clause, duplicates are dropped, complementary literals satisfy the clause, and satisfied
  clauses are not emitted.

As for `R7lean/Enc/NMH.lean`, none of this is verified: the CNF is `cnfOf (ctx s) 7
(items s)`; definition clauses are justified by `.tri`, the others by `.kset`. Since the
3-cycle variables are numbered on the fly, the context (`ctx`) is computed by a first pass
of the same generator (`finalState`).
-/

namespace R7.Enc.Tri

/-- `TRUE_LIT` / `FALSE_LIT` of the C program. -/
def TRUE : Int := 2147483647
def FALSE : Int := -2147483647

structure Env where
  n : Nat
  k : Nat
  /-- `fxA[u * n + w]`: `1` if `u → w` fixed, `-1` if `w → u` fixed, `0` if free -/
  fxA : Array Int
  /-- `avar[a * n + b]` (`a < b`): the variable of the free pair, else `0` -/
  avar : Array Nat
  /-- the free pairs in variable order -/
  pairs : Array (Nat × Nat)
  prefixes : Array (Nat × Nat)

@[inline] def Env.f (e : Env) (u w : Nat) : Int := e.fxA[u * e.n + w]!

def mkEnv (n k : Nat) (fx : Nat → Nat → Option Bool) : Env := Id.run do
  let mut fxA := Array.replicate (n * n) (0 : Int)
  for i in [0:n] do
    for j in [i + 1:n] do
      match fx i j with
      | some true => fxA := (fxA.set! (i * n + j) 1).set! (j * n + i) (-1)
      | some false => fxA := (fxA.set! (i * n + j) (-1)).set! (j * n + i) 1
      | none => pure ()
  let mut avar := Array.replicate (n * n) 0
  let mut pairs : Array (Nat × Nat) := #[]
  for i in [0:n] do
    for j in [i + 1:n] do
      if fxA[i * n + j]! == 0 then
        pairs := pairs.push (i, j)
        avar := avar.set! (i * n + j) pairs.size
  let mut prefixes : Array (Nat × Nat) := #[]
  for a in [0:n + 1 - k] do
    for b in [a + 1:n + 2 - k] do
      prefixes := prefixes.push (a, b)
  return { n, k, fxA, avar, pairs, prefixes }

/-- `lit(u, v)`: the literal "`u → v`", or `TRUE`/`FALSE` for a fixed pair. -/
@[inline] def Env.lit (e : Env) (u v : Nat) : Int :=
  let f := e.f u v
  if f == 1 then TRUE else if f == -1 then FALSE
  else
    let a := min u v
    let b := max u v
    let x : Int := e.avar[a * e.n + b]!
    if u < v then x else -x

/-- A clause under construction (`clsbuf`, `clssat`). -/
structure Cls where
  buf : Array Int := #[]
  sat : Bool := false

/-- `cls_add`. -/
@[inline] def Cls.add (c : Cls) (l : Int) : Cls :=
  if l == TRUE then { c with sat := true }
  else if l == FALSE then c
  else if c.buf.contains l then c
  else if c.buf.contains (-l) then { c with sat := true }
  else { c with buf := c.buf.push l }

/-- The generator state: the 3-cycle variables created so far. -/
structure St where
  /-- `tvar[a * n * n + b * n + c]`: the variable of the triple `a < b < c`, or `0` -/
  tvar : Array Nat
  /-- number of variables so far -/
  nv : Nat
  /-- the triples of the 3-cycle variables, in creation order -/
  tlist : Array (Nat × Nat × Nat)

def St.init (e : Env) : St :=
  { tvar := Array.replicate (e.n * e.n * e.n) 0, nv := e.pairs.size, tlist := #[] }

abbrev Out := Array (List Int × Just)

/-- `cls_end`: emit unless satisfied. -/
@[inline] def emit (out : Out) (c : Cls) (j : Just) : Out :=
  if c.sat then out else out.push (c.buf.toList, j)

/-- `cyc_lit(a, b, c)`. -/
def cycLit (e : Env) (a0 b0 c0 : Nat) (st : St) (out : Out) : Int × St × Out := Id.run do
  -- sort
  let (a, b) := if a0 > b0 then (b0, a0) else (a0, b0)
  let (b, c) := if b > c0 then (c0, b) else (b, c0)
  let (a, b) := if a > b then (b, a) else (a, b)
  let v := #[a, b, c]
  for i in [0:3] do
    let x := v[i]!
    let y := v[(i + 1) % 3]!
    let z := v[(i + 2) % 3]!
    if e.f x y == 1 && e.f x z == 1 then return (FALSE, st, out)
    if e.f x y == -1 && e.f x z == -1 then return (FALSE, st, out)
  let nfree := (if e.f a b == 0 then 1 else 0) + (if e.f a c == 0 then 1 else 0) +
    (if e.f b c == 0 then 1 else 0)
  if nfree == 0 then return (TRUE, st, out)
  if nfree == 1 then
    let mut x := v[0]!
    let mut z := v[0]!
    let mut found := false
    for i in [0:3] do
      for j in [0:3] do
        for l in [0:3] do
          if i == j || j == l || i == l then continue
          if e.f v[i]! v[j]! == 1 && e.f v[j]! v[l]! == 1 then
            x := v[i]!
            z := v[l]!
            found := true
    -- (`found` is always true here; the C program exits otherwise)
    return (if found then e.lit z x else FALSE, st, out)
  let id := a * e.n * e.n + b * e.n + c
  let t := st.tvar[id]!
  if t != 0 then return ((t : Int), st, out)
  let tv := st.nv + 1
  let st := { tvar := st.tvar.set! id tv, nv := tv, tlist := st.tlist.push (a, b, c) }
  let mut out := out
  for cyc in [#[a, b, c], #[a, c, b]] do
    for i in [0:3] do
      let x := cyc[i]!
      let y := cyc[(i + 1) % 3]!
      let z := cyc[(i + 2) % 3]!
      let cl := ((({} : Cls).add (-(tv : Int))).add (-(e.lit x y))).add (e.lit y z)
      out := emit out cl (.tri a b c)
  return ((tv : Int), st, out)

/-- `ext_rec` with `limit = 1`: the number of orderings found (stopping after `2`) and the
first one (`ord[depth]` = index into `S` of the vertex at that depth). -/
def extRec (e : Env) (S : Array Nat) :
    Nat → Nat → Nat → Array Nat → Nat × Array Nat → Nat × Array Nat
  | 0, _, _, _, acc => acc
  | f + 1, depth, remaining, ord, acc => Id.run do
    if acc.1 > 1 then return acc
    if depth == e.k then
      return (acc.1 + 1, if acc.1 == 0 then ord else acc.2)
    let mut acc := acc
    for i in [0:e.k] do
      if !(remaining.testBit i) then continue
      let x := S[i]!
      let mut ok := true
      for j in [0:e.k] do
        if j != i && remaining.testBit j && e.f S[j]! x == 1 then ok := false
      if !ok then continue
      acc := extRec e S f (depth + 1) (remaining ^^^ (1 <<< i)) (ord.set! depth i) acc
      if acc.1 > 1 then return acc
    return acc

/-- `handle_kset`. -/
def handleKset (e : Env) (S : Array Nat) (st : St) (out : Out) : St × Out := Id.run do
  let k := e.k
  let (cnt, ord) := extRec e S (k + 1) 0 ((1 <<< k) - 1) (Array.replicate k 0) (0, #[])
  if cnt == 0 then return (st, out)
  let just := Just.kset S.toList
  if cnt ≤ 1 then
    -- the clause forbidding the unique ordering: free pairs in row-major order
    let mut pos := Array.replicate k 0
    for p in [0:k] do
      pos := pos.set! ord[p]! p
    let mut cl : Cls := {}
    for i in [0:k] do
      for j in [i + 1:k] do
        if e.f S[i]! S[j]! == 0 then
          let l := e.lit S[i]! S[j]!
          cl := cl.add (if pos[i]! < pos[j]! then -l else l)
    return (st, emit out cl just)
  -- the 3-cycle clause
  let mut st := st
  let mut out := out
  let mut lits : Array Int := #[]
  let mut sat := false
  for a in [0:k] do
    for b in [a + 1:k] do
      for c in [b + 1:k] do
        let (l, st', out') := cycLit e S[a]! S[b]! S[c]! st out
        st := st'
        out := out'
        if l == TRUE then sat := true
        else if l != FALSE then lits := lits.push l
  if sat then return (st, out)
  let cl := lits.foldl Cls.add {}
  return (st, emit out cl just)

/-- `closes_fixed_cycle(d, x)`. -/
def closesFixedCycle (e : Env) (S : Array Nat) (d x : Nat) : Bool := Id.run do
  for i in [0:d] do
    for j in [i + 1:d] do
      let a := S[i]!
      let b := S[j]!
      if e.f a b == 0 || e.f b x == 0 || e.f x a == 0 then continue
      if e.f a b == 1 && e.f b x == 1 && e.f x a == 1 then return true
      if e.f a b == -1 && e.f b x == -1 && e.f x a == -1 then return true
  return false

/-- `comb_rec(d, start)`. -/
def combRec (e : Env) : Nat → Nat → Nat → Array Nat → St → Out → Array Nat × St × Out
  | 0, _, _, S, st, out => (S, st, out)
  | f + 1, d, start, S, st, out =>
    if d == e.k then
      let (st, out) := handleKset e S st out
      (S, st, out)
    else Id.run do
      let mut S := S
      let mut st := st
      let mut out := out
      for x in [start:e.n + 1 - (e.k - d)] do
        if closesFixedCycle e S d x then continue
        S := S.set! d x
        let r := combRec e f (d + 1) (x + 1) S st out
        S := r.1
        st := r.2.1
        out := r.2.2
      return (S, st, out)

/-- Block `t`: the `7`-sets whose two smallest vertices are `prefixes[t]` (no prefix of length
`≤ 2` is pruned, since a fixed 3-cycle needs three vertices). -/
def step (e : Env) (st : St) (t : Nat) : St × Out :=
  let (a, b) := e.prefixes[t]!
  let S := ((Array.replicate e.k 0).set! 0 a).set! 1 b
  let r := combRec e (e.k + 1) 2 (b + 1) S st #[]
  r.2

def nblocks (e : Env) : Nat := e.prefixes.size

def env (s : PivotSpec) : Env := mkEnv s.n 7 s.fx

/-- The state after all blocks (first pass): the 3-cycle variables. -/
def final (s : PivotSpec) : St :=
  let e := env s
  finalState (step e) (St.init e) 0 (nblocks e)

/-- The context, from the first pass: variables `1..F` are the free pairs, `F + 1 + i` the
`i`-th 3-cycle variable. -/
def ctxOf (s : PivotSpec) (e : Env) (st : St) : Ctx :=
  let F := e.pairs.size
  { n := s.n, fx := s.fx,
    dec := fun v =>
      if 1 ≤ v ∧ v ≤ F then
        let p := e.pairs[v - 1]!
        .arc p.1 p.2
      else if F < v ∧ v - F - 1 < st.tlist.size then
        let t := st.tlist[v - F - 1]!
        .tri t.1 t.2.1 t.2.2
      else .none }

def ctx (s : PivotSpec) : Ctx := ctxOf s (env s) (final s)

/-- The items of the encoding (unverified generator, second pass). -/
def items (s : PivotSpec) : List (List Int × Just) :=
  let e := env s
  runBlocks (step e) (St.init e) 0 (nblocks e)

/-- **The 3-cycle encoding** (`src/encode.c`, `k = 7`, `limit = 1`) of `TT₇` exclusion for a
pivot instance: the clauses of the items that pass the certified checks. -/
def cnf (s : PivotSpec) : List (List Int) :=
  cnfOf (ctx s) 7 (items s)

/-- The number of variables in the header (`nvars` of the C program). -/
def numVars (s : PivotSpec) : Nat := (final s).nv

end R7.Enc.Tri
