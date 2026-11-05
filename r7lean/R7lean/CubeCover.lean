import R7lean.EncSound

/-!
# The cube cover lemma (`paper/r7le46.tex`, Lemma `lem:cover`)

Cube-and-conquer (`paper/r7le46.tex` §7) solves `F` as the formulas `F ∧ c` for cubes `c`, and
`scripts/cnc_summary.py` checks:
1. *level-0 cover*: the formula `⋀_c ¬c` over the level-0 cubes is unsatisfiable;
2. *splits*: the children of a split cube `c` are exactly the `2^S` cubes `c ++ σ`, `σ` ranging
   over the sign patterns on one sequence of `S` variables;
3. *leaves*: every cube without children has `F ∧ c` unsatisfiable (an accepted LRAT proof).

`Closed F c` is the inductive form of 2–3, and `unsat_of_cover` is the lemma: under 1–3, `F` is
unsatisfiable. So each CNF axiom of `R7lean/FactsCNF.lean` follows from the per-leaf facts
`¬ Satisfiable (withCube F c)`, which is what the checked LRAT proofs establish, together with
the cover formula of 1 (also checked by an LRAT proof) and the tree structure of 2. A compiled
check of a results directory against `cubes.icnf` is not part of this milestone.

Everything here is proved in the kernel (no axioms beyond Lean's).
-/

namespace R7.Enc

/-- A cube (a conjunction of literals) holds. -/
def CubeHolds (τ : Nat → Bool) (c : List Int) : Prop :=
  ∀ l ∈ c, litHolds τ l = true

/-- `F ∧ c`: `F` plus one unit clause per literal of the cube (the input of each cube run). -/
def withCube (F : List (List Int)) (c : List Int) : List (List Int) :=
  F ++ c.map fun l => [l]

/-- The clause `¬c`. -/
def negCube (c : List Int) : List Int :=
  c.map fun l => -l

/-- The literals of the sign pattern `s` on the variables `vs` (`true`: positive). -/
def signLits (vs : List Nat) (s : List Bool) : List Int :=
  (vs.zip s).map fun p => if p.2 then (p.1 : Int) else -(p.1 : Int)

/-- A cube is closed: a leaf with `F ∧ c` unsatisfiable, or split on the variables `vs` (all
nonzero) into the `2^|vs|` cubes `c ++ signLits vs s`, each closed. -/
inductive Closed (F : List (List Int)) : List Int → Prop
  | leaf {c : List Int} : ¬ Satisfiable (withCube F c) → Closed F c
  | split {c : List Int} (vs : List Nat) (hvs : ∀ v ∈ vs, 0 < v) :
      (∀ s : List Bool, s.length = vs.length → Closed F (c ++ signLits vs s)) → Closed F c

theorem cubeHolds_signLits (τ : Nat → Bool) :
    ∀ (vs : List Nat), (∀ v ∈ vs, 0 < v) → CubeHolds τ (signLits vs (vs.map τ))
  | [], _ => by simp [CubeHolds, signLits]
  | v :: vs, h => by
    intro l hl
    simp only [signLits, List.map_cons, List.zip_cons_cons, List.mem_cons] at hl
    rcases hl with rfl | hl
    · have hv : 0 < v := h v (by simp)
      cases hτ : τ v <;> simp [litHolds, hτ, hv]
    · exact cubeHolds_signLits τ vs (fun w hw => h w (by simp [hw])) l hl

theorem litHolds_neg (τ : Nat → Bool) {l : Int} (hl : l ≠ 0) :
    litHolds τ (-l) = !litHolds τ l := by
  unfold litHolds
  rw [Int.natAbs_neg]
  rcases Int.lt_or_gt_of_ne hl with h | h
  · have h1 : ¬ (0 < l) := by omega
    have h2 : 0 < -l := by omega
    rw [ite_eq_left h2, ite_eq_right h1, Bool.not_not]
  · have h2 : ¬ (0 < -l) := by omega
    rw [ite_eq_right h2, ite_eq_left h]

/-- An assignment that satisfies a closed cube falsifies `F`. -/
theorem Closed.falsifies {F : List (List Int)} {c : List Int} (h : Closed F c) (τ : Nat → Bool)
    (hc : CubeHolds τ c) : ¬ ∀ cl ∈ F, ∃ l ∈ cl, litHolds τ l = true := by
  induction h with
  | @leaf c hunsat =>
    intro hF
    apply hunsat
    refine ⟨τ, fun cl hcl => ?_⟩
    rcases List.mem_append.1 hcl with hcl | hcl
    · exact hF cl hcl
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hcl
      exact ⟨l, by simp, hc l hl⟩
  | @split c vs hvs _ ih =>
    apply ih (vs.map τ) (by simp)
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hc l hl
    · exact cubeHolds_signLits τ vs hvs l hl

/-- **Cube cover lemma.** If the clauses `¬c` of the level-0 cubes (all literals nonzero) form
an unsatisfiable formula and every level-0 cube is closed, then `F` is unsatisfiable. -/
theorem unsat_of_cover {F : List (List Int)} (cubes : List (List Int))
    (hnz : ∀ c ∈ cubes, ∀ l ∈ c, l ≠ 0)
    (hcover : ¬ Satisfiable (cubes.map negCube))
    (hclosed : ∀ c ∈ cubes, Closed F c) : ¬ Satisfiable F := by
  rintro ⟨τ, hF⟩
  -- `τ` satisfies some level-0 cube
  have : ∃ c ∈ cubes, CubeHolds τ c := by
    by_contra hno
    apply hcover
    refine ⟨τ, fun cl hcl => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcl
    have : ¬ CubeHolds τ c := fun h => hno ⟨c, hc, h⟩
    simp only [CubeHolds, not_forall] at this
    obtain ⟨l, hl, hfalse⟩ := this
    refine ⟨-l, List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
    rw [litHolds_neg τ (hnz c hc l hl)]
    simpa using hfalse
  obtain ⟨c, hc, hτ⟩ := this
  exact (hclosed c hc).falsifies τ hτ hF

end R7.Enc
