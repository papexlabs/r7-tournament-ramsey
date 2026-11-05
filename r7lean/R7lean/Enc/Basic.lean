/-!
# DIMACS-level CNF semantics and certified clause checks (no Mathlib)

This file and the other `R7lean/Enc/*.lean` files import only Lean core, so that the
executable `r7encode` (which evaluates the encoders) does not link Mathlib.

## CNF model

A DIMACS literal is an `Int` (`v` or `-v` for a variable `v ≥ 1`), a clause is a `List Int`,
a CNF is a `List (List Int)`; an assignment is a function `Nat → Bool`. `Satisfiable F` says
that some assignment makes some literal of every clause true. The header line `p cnf V C`
is not part of the semantics (it only bounds the variables and counts the clauses).

## Certified clause checks

The encoders of `R7lean/Enc/Tri.lean` and `R7lean/Enc/NMH.lean` generate *items*
`(clause, justification)` by code that is not verified; the CNF is defined as the clauses of
the items that pass `checkItem` (`cnfOf`). Every check is local and cheap, and
`R7lean/EncSound.lean` proves that a clause passing it is satisfied by the canonical
assignment `τ_C` of every `TT_k`-free tournament `C` compatible with the fixed arcs. The
generators are meant to reproduce the C encoders exactly; that is established by the sha256
of the produced files (the executable also reports the number of items that failed a check,
which must be `0`).

A pair of vertices is described by a *context* `Ctx`:
* `fx u w : Option Bool`: the fixed arc between `u` and `w` (`some true` iff `u → w` is
  fixed, `some false` iff `w → u` is fixed, `none` if the pair is free);
* `dec v : VarMeaning`: the meaning of variable `v`, either the arc `u → w` or "the triple
  `a < b < c` is a 3-cycle".

Justifications:
* `.fixed`: some literal of the clause is made true by a fixed arc;
* `.kset S`: `S` is a set of `k` vertices; every 3-cycle orientation of every triple of `S`
  that is consistent with the fixed arcs makes some literal of the clause true. Sound for
  `TT_k`-free `C`: `S` is not transitive in `C`, so some triple of `S` is a 3-cycle in `C`.
  (This covers the "direct" clauses of both encoders, which forbid the transitive
  orientations of `S`, and the "3-cycle" clauses of `src/encode.c`.)
* `.tri a b c`: every orientation of the triple consistent with the fixed arcs makes some
  literal true (the definitions of the 3-cycle variables). Sound for every `C`.
-/

namespace R7.Enc

/-! ### CNF semantics -/

/-- The value of a DIMACS literal under an assignment. -/
def litHolds (τ : Nat → Bool) (l : Int) : Bool :=
  if 0 < l then τ l.natAbs else !τ l.natAbs

/-- A CNF (list of clauses, each a list of DIMACS literals) is satisfiable. -/
def Satisfiable (F : List (List Int)) : Prop :=
  ∃ τ : Nat → Bool, ∀ c ∈ F, ∃ l ∈ c, litHolds τ l = true

/-! ### Contexts -/

/-- The meaning of a variable under the canonical interpretation. -/
inductive VarMeaning where
  /-- the arc `u → w` -/
  | arc (u w : Nat)
  /-- the triple `a < b < c` is a 3-cycle -/
  | tri (a b c : Nat)
  /-- unused variable -/
  | none
  deriving Inhabited, Repr, BEq

/-- Fixed arcs and the meaning of the variables, on the vertices `0, …, n - 1`. -/
structure Ctx where
  n : Nat
  fx : Nat → Nat → Option Bool
  dec : Nat → VarMeaning

/-- Justification of an item. -/
inductive Just where
  | fixed
  | kset (S : List Nat)
  | tri (a b c : Nat)
  deriving Inhabited, Repr

/-! ### Orientations of a triple -/

/-- An orientation of a triple `a < b < c`: `(a → b, a → c, b → c)`. -/
abbrev Ori := Bool × Bool × Bool

/-- The orientation is a 3-cycle (`a → b → c → a` or `a → c → b → a`). -/
def cyclicB (o : Ori) : Bool :=
  (o.1 && o.2.2 && !o.2.1) || (!o.1 && !o.2.2 && o.2.1)

/-- All eight orientations. -/
def allOri : List Ori :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

/-- A fixed-arc entry agrees with a value. -/
def agree : Option Bool → Bool → Bool
  | none, _ => true
  | some v, w => v == w

/-- The value of the arc `u → w` in the orientation `o` of the triple `a, b, c`, if `{u, w}` is
one of its pairs. -/
def locVal (a b c : Nat) (o : Ori) (u w : Nat) : Option Bool :=
  if u == a && w == b then some o.1
  else if u == b && w == a then some !o.1
  else if u == a && w == c then some o.2.1
  else if u == c && w == a then some !o.2.1
  else if u == b && w == c then some o.2.2
  else if u == c && w == b then some !o.2.2
  else none

/-- The literal `l` is true in the orientation `o` of the triple `a < b < c`, judged from the
triple alone. -/
def litLocal (dec : Nat → VarMeaning) (a b c : Nat) (o : Ori) (l : Int) : Bool :=
  match dec l.natAbs with
  | .arc u w =>
    match locVal a b c o u w with
    | some v => v == decide (0 < l)
    | none => false
  | .tri a' b' c' => a' == a && b' == b && c' == c && cyclicB o == decide (0 < l)
  | .none => false

/-- Every orientation of the triple `a < b < c` that is consistent with the fixed arcs (and is a
3-cycle, if `cyclicOnly`) makes some literal of `cl` true. -/
def triOK (ctx : Ctx) (a b c : Nat) (cl : List Int) (cyclicOnly : Bool) : Bool :=
  let f1 := ctx.fx a b
  let f2 := ctx.fx a c
  let f3 := ctx.fx b c
  allOri.all fun o =>
    !(agree f1 o.1 && agree f2 o.2.1 && agree f3 o.2.2) || (cyclicOnly && !cyclicB o) ||
      cl.any (litLocal ctx.dec a b c o)

/-- `g b c` for all `b, c` occurring in this order in the list. -/
def allPairs (g : Nat → Nat → Bool) : List Nat → Bool
  | [] => true
  | b :: r => r.all (g b) && allPairs g r

/-- `f a b c` for all `a, b, c` occurring in this order in the list. -/
def allTriples (f : Nat → Nat → Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: r => allPairs (f a) r && allTriples f r

/-- The check for `.kset S`. -/
def ksetOK (ctx : Ctx) (k : Nat) (S : List Nat) (cl : List Int) : Bool :=
  S.length == k && S.all (· < ctx.n) && decide (S.Pairwise (· < ·)) &&
    allTriples (fun a b c => triOK ctx a b c cl true) S

/-- The check for `.fixed`. -/
def fixedOK (ctx : Ctx) (cl : List Int) : Bool :=
  cl.any fun l =>
    match ctx.dec l.natAbs with
    | .arc u w => decide (u < ctx.n) && decide (w < ctx.n) && u != w &&
        ctx.fx u w == some (decide (0 < l))
    | _ => false

/-- The check for `.tri a b c`. -/
def tdefOK (ctx : Ctx) (a b c : Nat) (cl : List Int) : Bool :=
  decide (a < b) && decide (b < c) && decide (c < ctx.n) && triOK ctx a b c cl false

/-- The certified check of an item. -/
def checkItem (ctx : Ctx) (k : Nat) : List Int × Just → Bool
  | (cl, .fixed) => fixedOK ctx cl
  | (cl, .kset S) => ksetOK ctx k S cl
  | (cl, .tri a b c) => tdefOK ctx a b c cl

/-- The CNF of a list of items: the clauses of the items that pass the check. -/
def cnfOf (ctx : Ctx) (k : Nat) (items : List (List Int × Just)) : List (List Int) :=
  (items.filter (checkItem ctx k)).map Prod.fst

/-! ### Block-structured generators

The encoders produce their items block by block (a block is a range of `k`-sets), with a state
threaded through the blocks (the 3-cycle variables already created). `runBlocks step s i m`
is the concatenation of the outputs of blocks `i, …, i + m - 1`; the executable runs the same
loop, writing each block's clauses instead of concatenating them. -/

/-- The items of blocks `i, i+1, …, i + m - 1`, starting in state `s`. -/
def runBlocks {σ β : Type} (step : σ → Nat → σ × Array β) : σ → Nat → Nat → List β
  | _, _, 0 => []
  | s, i, m + 1 =>
    let r := step s i
    r.2.toList ++ runBlocks step r.1 (i + 1) m

/-- The state after blocks `i, …, i + m - 1`. -/
def finalState {σ β : Type} (step : σ → Nat → σ × Array β) : σ → Nat → Nat → σ
  | s, _, 0 => s
  | s, i, m + 1 => finalState step (step s i).1 (i + 1) m

/-! ### Pivot instances -/

/-- The tournament given by the upper triangle of a 0/1 matrix with row bitmasks `rows`
(as `Tournament.ofRows`): for `i < j`, `i → j` iff bit `j` of row `i` is set. -/
def upperArc (rows : List Nat) (i j : Nat) : Bool :=
  if i < j then (rows.getD i 0).testBit j
  else if j < i then !(rows.getD j 0).testBit i
  else false

/-- A pivot instance `X -p- Z` with `|X| = a`, `|Z| = b`, on the vertices `0, …, a + b`:
`X` is `0, …, a - 1`, the pivot is `a`, `Z` is `a + 1, …, a + b`. `xArc` and `zArc` are the
arcs of `X` and `Z` (with their own vertex numbering). -/
structure PivotSpec where
  a : Nat
  b : Nat
  xArc : Nat → Nat → Bool
  zArc : Nat → Nat → Bool

/-- The number of vertices `a + 1 + b`. -/
def PivotSpec.n (s : PivotSpec) : Nat := s.a + 1 + s.b

/-- The fixed arcs of the pivot instance: inside `X` and inside `Z` as given, `X → p → Z`,
and the pairs between `X` and `Z` free. -/
def PivotSpec.fx (s : PivotSpec) (u w : Nat) : Option Bool :=
  if u < s.a then
    if w < s.a then some (s.xArc u w) else if w = s.a then some true else none
  else if u = s.a then
    if w < s.a then some false else if w = s.a then none else some true
  else
    if w < s.a then none else if w = s.a then some false
    else some (s.zArc (u - s.a - 1) (w - s.a - 1))

end R7.Enc
