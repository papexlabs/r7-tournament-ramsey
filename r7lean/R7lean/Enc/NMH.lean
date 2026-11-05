import R7lean.Enc.Basic

/-!
# NMH's direct encoder `tour-encode.c` (Stage 4), reproduced in Lean (no Mathlib)

`refs/directed-ramsey-src/Directed-Ramsey-master/encoding/tour-encode.c` (sha256
`a6d67708…` in `data/stage4_manifest.json`), run by `scripts/stage4_instances.py` as
`tour-encode N 7 INPUT 5040`, i.e. with `limit = 7! = 5040`, so the 3-cycle branch and the
auxiliary 3-cycle definitions of the C program are never used and are not reproduced here.

What the C program prints, in order (vertices `1..n`, as in the C code):
1. for `i, j = 1..n` (row-major) with the arc `i → j` fixed: the unit clause `getEdge(i, j)`;
2. for every `7`-set `o₁ < … < o₇` (lexicographic order) that does not contain a fixed
   3-cycle: all permutations of the set (Heap's algorithm, in its order) whose fixed arcs all
   point backwards are listed as bit masks over the free pairs of the set (bit `s` for the
   `s`-th free pair in variable order: bit set iff the smaller vertex beats the larger);
   then the reduction loop of `printClause` turns the list into "reduced clauses"
   `printReducedClause(mask, xor)` (the cube of the masks that agree with `mask` outside
   `xor`, negated).
Variable of the pair `{u < v}`: `getEdge u v = u + (v - 2)(v - 1)/2`, positive for `u → v`.

The enumeration of Heap's algorithm is pruned: a call that permutes the first `s` positions
can only produce rejected permutations if an element among the first `s` positions has a
fixed arc to the element at position `s`; such a call is skipped and its net effect on the
array (a fixed permutation of the first `s` positions, `heapEff`) applied instead. This
changes nothing in the list of accepted masks or its order.

None of this is verified: the CNF is `cnfOf (nmhCtx s) 7 (nmhItems s)`, whose clauses are the
items that pass the certified checks of `R7lean/Enc/Basic.lean`; the units are justified by
`.fixed`, the reduced clauses by `.kset` (the 7-set).
-/

namespace R7.Enc.NMH

/-- `getEdge a b` (1-indexed vertices): `+var` for `a → b`, `-var` for `b → a`. -/
def getEdge (a b : Nat) : Int :=
  let mn := min a b
  let mx := max a b
  let res : Int := (mn + (mx - 2) * (mx - 1) / 2 : Nat)
  if a < b then res else -res

/-- Heap's algorithm on the first `s` positions, without pruning (`permutations` of the C
program with every leaf ignored). -/
def heapSim : Nat → Array Nat → Array Nat
  | 0, a => a
  | 1, a => a
  | s + 2, a => Id.run do
    let t := s + 2
    let mut a := heapSim (s + 1) a
    for i in [0:t - 1] do
      if t % 2 == 0 then a := a.swapIfInBounds i (t - 1) else a := a.swapIfInBounds 0 (t - 1)
      a := heapSim (s + 1) a
    return a

/-- `heapEff[s]`: the arrangement of positions `0..s-1` after Heap's algorithm on `s`
positions (position `i` then holds the element that was at position `heapEff[s][i]`). -/
def heapEff (k : Nat) : Array (Array Nat) :=
  (List.range (k + 1)).toArray.map fun s => heapSim s (List.range s).toArray

/-- Rearrange the first `s` positions of `order` by `eff`. -/
def applyEff (eff : Array Nat) (order : Array Nat) : Array Nat := Id.run do
  let old := order
  let mut order := order
  for i in [0:eff.size] do
    order := order.set! i (old[eff[i]!]!)
  return order

/-- The data of one instance, computed once. `M` is the `(n+1) × (n+1)` matrix of the C
program (1-indexed; `1`: `i → j` fixed, `-1`: `j → i` fixed, `0`: free; diagonal `-1`). -/
structure Env where
  n : Nat
  k : Nat
  limit : Nat
  M : Array Int
  eff : Array (Array Nat)
  prefixes : Array (Nat × Nat)

/-- `M[i][j]`. -/
@[inline] def Env.m (e : Env) (i j : Nat) : Int := e.M[i * (e.n + 1) + j]!

/-- The matrix from the fixed arcs, read from the upper triangle (as the C program reads its
input file). -/
def mkMatrix (n : Nat) (fx : Nat → Nat → Option Bool) : Array Int := Id.run do
  let w := n + 1
  let mut M := Array.replicate (w * w) (0 : Int)
  for i in [1:n + 1] do
    M := M.set! (i * w + i) (-1)
  for i in [1:n + 1] do
    for j in [i + 1:n + 1] do
      match fx (i - 1) (j - 1) with
      | some true => M := (M.set! (i * w + j) 1).set! (j * w + i) (-1)
      | some false => M := (M.set! (i * w + j) (-1)).set! (j * w + i) 1
      | none => pure ()
  return M

def mkEnv (n k : Nat) (fx : Nat → Nat → Option Bool) : Env :=
  let prefixes := Id.run do
    let mut ps : Array (Nat × Nat) := #[]
    for a in [1:n + 1] do
      for b in [a + 1:n + 1] do
        ps := ps.push (a, b)
    return ps
  { n, k, limit := (List.range k).foldl (fun acc i => acc * (i + 1)) 1, M := mkMatrix n fx,
    eff := heapEff k, prefixes }

/-- The pruned Heap's algorithm. `S` is the 7-set (1-indexed vertices, increasing), `order`
the current arrangement (indices into `S`), `fps` the free pairs (index pairs `(i, j)`,
`i < j`, in variable order). Returns the new arrangement and the list of accepted masks. -/
def perms (e : Env) (S : Array Nat) (fps : Array (Nat × Nat)) :
    Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, order, list => (order, list)
  | s + 1, order, list =>
    let sz := s + 1
    let bad : Bool :=
      sz < e.k && Id.run do
        let y := S[order[sz]!]!
        let mut b := false
        for a in [0:sz] do
          if e.m S[order[a]!]! y == 1 then b := true
        return b
    if bad then (applyEff e.eff[sz]! order, list)
    else if sz == 1 then
      -- a leaf: every fixed arc points backwards; record the mask
      let pos := Id.run do
        let mut pos := Array.replicate e.k 0
        for p in [0:e.k] do
          pos := pos.set! order[p]! p
        return pos
      let mask := Id.run do
        let mut m := 0
        for t in [0:fps.size] do
          let (i, j) := fps[t]!
          if pos[j]! < pos[i]! then m := m ||| (1 <<< t)
        return m
      (order, list.push mask)
    else Id.run do
      let (o, l) := perms e S fps s order list
      let mut order := o
      let mut list := l
      for i in [0:sz - 1] do
        if sz % 2 == 0 then order := order.swapIfInBounds i (sz - 1)
        else order := order.swapIfInBounds 0 (sz - 1)
        let (o, l) := perms e S fps s order list
        order := o
        list := l
      return (order, list)

/-- `x` is a power of two. -/
@[inline] def isPow2 (x : Nat) : Bool := x != 0 && (x &&& (x - 1)) == 0

/-- `extendXOR` of the C program. -/
def extendXOR (list : Array Nat) (mask xor : Nat) : Nat := Id.run do
  for i in [0:list.size] do
    let x := mask ^^^ list[i]!
    if (xor ||| x) == xor then continue
    if isPow2 x then
      for j in [0:list.size] do
        if list[j]! == mask ^^^ (xor ||| x) then return x
  return 0

/-- Repeated `extendXOR` until it returns `0` (at most `fuel` steps; each step adds a bit). -/
def extendFull (list : Array Nat) (mask : Nat) : Nat → Nat → Nat
  | 0, xor => xor
  | f + 1, xor =>
    let x := extendXOR list mask xor
    if x == 0 then xor else extendFull list mask f (xor ||| x)

/-- `printReducedClause(order, mask, xor)`: the literals of the free pairs outside `xor`. -/
def reducedClause (vars : Array Int) (mask xor : Nat) : List Int := Id.run do
  let mut cl : Array Int := #[]
  for t in [0:vars.size] do
    if !(xor.testBit t) then
      cl := cl.push (if mask.testBit t then -vars[t]! else vars[t]!)
  return cl.toList

/-- The clauses of one 7-set (`printClause` of the C program). -/
def ksetClauses (e : Env) (S : Array Nat) : Array (List Int) := Id.run do
  let k := e.k
  -- 1. a fixed 3-cycle: no clause
  for a in [0:k] do
    for b in [a + 1:k] do
      for c in [b + 1:k] do
        let m := e.m S[a]! S[b]!
        if m == -(e.m S[a]! S[c]!) && m == e.m S[b]! S[c]! && m != 0 then return #[]
  -- free pairs in variable order (`b` outer, `a` inner)
  let mut fps : Array (Nat × Nat) := #[]
  let mut vars : Array Int := #[]
  for b in [0:k] do
    for a in [0:b] do
      if e.m S[a]! S[b]! == 0 then
        fps := fps.push (a, b)
        vars := vars.push (getEdge S[a]! S[b]!)
  -- 2. the accepted permutations, in the order of Heap's algorithm
  let (_, list) := perms e S fps k (List.range k).toArray #[]
  let L := list.size
  let nfp := fps.size
  -- 3. the reduction loop
  let mut out : Array (List Int) := #[]
  let mut mark := Array.replicate L false
  let mut iter := true
  for _ in [0:L + 2] do
    if !iter then break
    iter := false
    for i in [0:L] do
      if mark[i]! then continue
      let li := list[i]!
      let mut xor := 0
      for j in [0:L] do
        if i != j then
          let x := li ^^^ list[j]!
          if isPow2 x then xor := xor ||| x
      let mut flag := false
      for j in [0:L] do
        if xor != 0 && list[j]! == li ^^^ xor then
          flag := true
          break
      if flag then
        xor := extendFull list li (nfp + 2) xor
        out := out.push (reducedClause vars li xor)
        iter := true
        for j in [0:L] do
          if (xor ||| (li ^^^ list[j]!)) == xor then mark := mark.set! j true
  if L ≤ e.limit then
    for i in [0:L] do
      if !mark[i]! then
        let li := list[i]!
        out := out.push (reducedClause vars li (extendFull list li (nfp + 2) 0))
  return out

/-- All 7-sets extending `S[0..d-1]` (lexicographic), with their clauses appended to `out`. -/
def enumRec (e : Env) : Nat → Nat → Array Nat → Array (List Int × Just) →
    Array Nat × Array (List Int × Just)
  | 0, _, S, out => (S, out)
  | f + 1, d, S, out =>
    if d == e.k then
      let cls := ksetClauses e S
      let just := Just.kset (S.toList.map (· - 1))
      (S, cls.foldl (fun o c => o.push (c, just)) out)
    else Id.run do
      let start := if d == 0 then 1 else S[d - 1]! + 1
      let mut S := S
      let mut out := out
      for x in [start:e.n + 1] do
        S := S.set! d x
        let r := enumRec e f (d + 1) S out
        S := r.1
        out := r.2
      return (S, out)

/-- Block `0`: the unit clauses of the fixed arcs; block `t ≥ 1`: the 7-sets whose two
smallest vertices are `prefixes[t - 1]`. -/
def step (e : Env) (_ : Unit) (t : Nat) : Unit × Array (List Int × Just) :=
  if t == 0 then
    ((), Id.run do
      let mut out : Array (List Int × Just) := #[]
      for i in [1:e.n + 1] do
        for j in [1:e.n + 1] do
          if e.m i j == 1 then out := out.push ([getEdge i j], .fixed)
      return out)
  else
    let (a, b) := e.prefixes[t - 1]!
    let S := ((Array.replicate e.k 0).set! 0 a).set! 1 b
    ((), (enumRec e (e.k + 1) 2 S #[]).2)

def nblocks (e : Env) : Nat := e.prefixes.size + 1

/-- The meaning of the variables: `getEdge u v ↦ (u - 1 → v - 1)` (0-indexed vertices). -/
def decTable (n : Nat) : Array VarMeaning := Id.run do
  let mut t := Array.replicate (n * (n - 1) / 2 + 1) VarMeaning.none
  for v in [2:n + 1] do
    for u in [1:v] do
      t := t.set! (u + (v - 2) * (v - 1) / 2) (.arc (u - 1) (v - 1))
  return t

/-- The context of the NMH encoding of a pivot instance. -/
def ctx (s : PivotSpec) : Ctx :=
  let t := decTable s.n
  { n := s.n, fx := s.fx, dec := fun v => t.getD v .none }

def env (s : PivotSpec) : Env := mkEnv s.n 7 s.fx

/-- The items of the NMH encoding of a pivot instance (unverified generator). -/
def items (s : PivotSpec) : List (List Int × Just) :=
  let e := env s
  runBlocks (step e) () 0 (nblocks e)

/-- **The NMH encoding** of `TT₇` exclusion for a pivot instance: the clauses of the items
that pass the certified checks. -/
def cnf (s : PivotSpec) : List (List Int) :=
  cnfOf (ctx s) 7 (items s)

end R7.Enc.NMH
