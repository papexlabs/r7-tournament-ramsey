import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Tournaments

A tournament on a vertex type `V` is an irreflexive relation `beats` such that for
distinct `u v` exactly one of `beats u v`, `beats v u` holds.

* Embeddings and isomorphisms of tournaments are Mathlib's relation embeddings
  `S.beats ↪r T.beats` and relation isomorphisms `S.beats ≃r T.beats`.
* `T.Contains S` : some embedding `S ↪ T` exists (`S` is an induced subtournament of `T`
  up to isomorphism).
* `TT k` is the transitive tournament on `Fin k` (`i` beats `j` iff `i < j`);
  `T.ContainsTT k := T.Contains (TT k)` and `T.TTFree k := ¬ T.ContainsTT k`.
  `containsTT_iff` restates `ContainsTT` as "some `f : Fin k → V` with `f i` beating `f j`
  whenever `i < j`", and `containsTT_iff_exists_transitive` as "some transitive set of
  `k` vertices".
* `T.comap f` is the pullback along an injective map, `T.induce S` the induced
  subtournament on a set, `T.reverse` the reversal.
* `inNbhd v` / `inFinset v` (vertices beating `v`, the in-neighbourhood `N⁻(v)`),
  `outNbhd v` / `outFinset v` (`N⁺(v)`), `indeg`, `outdeg`, and the averaging lemma
  `exists_le_outdeg` (some vertex has out-degree `≥ m` when `|V| ≥ 2m`).
* `ofUpper r` / `ofRows rows`: the tournament on `Fin n` read from the upper triangle of a
  0/1 matrix with row bitmasks `r i` (used for the named tournaments of `R7lean/Data.lean`).
-/

namespace R7

/-- A tournament on the vertex type `V`. `beats u v` is the arc `u → v`. -/
structure Tournament (V : Type*) where
  /-- `beats u v`: the arc between `u` and `v` points from `u` to `v`. -/
  beats : V → V → Prop
  irrefl : ∀ v, ¬ beats v v
  asymm : ∀ {u v}, beats u v → ¬ beats v u
  total : ∀ {u v}, u ≠ v → beats u v ∨ beats v u

namespace Tournament

variable {V W U : Type*}

theorem ne_of_beats (T : Tournament V) {u v : V} (h : T.beats u v) : u ≠ v := by
  rintro rfl
  exact T.irrefl u h

/-! ### Embeddings, containment, pullback, reversal -/

/-- `T` contains `S`: there is an embedding of tournaments `S ↪ T`. -/
def Contains (T : Tournament V) (S : Tournament W) : Prop :=
  Nonempty (S.beats ↪r T.beats)

/-- Between tournaments, every map that preserves `beats` is an embedding. -/
def embOfHom (S : Tournament W) (T : Tournament V) (f : W → V)
    (hf : ∀ a b, S.beats a b → T.beats (f a) (f b)) : S.beats ↪r T.beats where
  toFun := f
  inj' := by
    intro a b hab
    by_contra hne
    rcases S.total hne with h | h
    · have h' := hf a b h
      rw [hab] at h'
      exact T.irrefl _ h'
    · have h' := hf b a h
      rw [hab] at h'
      exact T.irrefl _ h'
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      by_cases hab : a = b
      · subst hab
        exact absurd h (T.irrefl _)
      · rcases S.total hab with h' | h'
        · exact h'
        · exact absurd (hf b a h') (T.asymm h)
    · exact hf a b

theorem Contains.trans {T : Tournament V} {S : Tournament W} {R : Tournament U}
    (h₁ : T.Contains S) (h₂ : S.Contains R) : T.Contains R := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₂.trans e₁⟩

/-- Pullback of a tournament along an injective map. -/
def comap (T : Tournament V) (f : W ↪ V) : Tournament W where
  beats a b := T.beats (f a) (f b)
  irrefl a := T.irrefl (f a)
  asymm h := T.asymm h
  total h := T.total (f.injective.ne h)

/-- The pullback embeds into the original tournament along `f`. -/
def comapEmb (T : Tournament V) (f : W ↪ V) : (T.comap f).beats ↪r T.beats :=
  ⟨f, Iff.rfl⟩

@[simp] theorem comapEmb_apply (T : Tournament V) (f : W ↪ V) (a : W) :
    T.comapEmb f a = f a := rfl

theorem contains_comap (T : Tournament V) (f : W ↪ V) : T.Contains (T.comap f) :=
  ⟨T.comapEmb f⟩

instance decComap (T : Tournament V) [DecidableRel T.beats] (f : W ↪ V) :
    DecidableRel (T.comap f).beats :=
  fun a b => inferInstanceAs (Decidable (T.beats (f a) (f b)))

/-- The induced subtournament on a set of vertices. -/
def induce (T : Tournament V) (S : Set V) : Tournament S :=
  T.comap (Function.Embedding.subtype _)

/-- The reversal: every arc reversed. -/
def reverse (T : Tournament V) : Tournament V where
  beats a b := T.beats b a
  irrefl a := T.irrefl a
  asymm h := T.asymm h
  total h := (T.total h).symm

/-- The tournament on `Fin n` read from the upper triangle of a 0/1 matrix whose row `i`
is the bitmask `r i`: for `i < j`, `i` beats `j` iff bit `j` of `r i` is set, and
otherwise `j` beats `i`. (The bits on and below the diagonal are ignored.) -/
def ofUpper {n : ℕ} (r : Fin n → ℕ) : Tournament (Fin n) where
  beats i j := (i < j ∧ (r i).testBit j = true) ∨ (j < i ∧ (r j).testBit i = false)
  irrefl i := by simp
  asymm := by
    intro i j h h'
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact lt_asymm h1 h3
    · rw [h2] at h4; exact absurd h4 (by simp)
    · rw [h2] at h4; exact absurd h4 (by simp)
    · exact lt_asymm h1 h3
  total := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · cases (r i).testBit j
      · exact Or.inr (Or.inr ⟨h, rfl⟩)
      · exact Or.inl (Or.inl ⟨h, rfl⟩)
    · cases (r j).testBit i
      · exact Or.inl (Or.inr ⟨h, rfl⟩)
      · exact Or.inr (Or.inl ⟨h, rfl⟩)

instance decOfUpper {n : ℕ} (r : Fin n → ℕ) : DecidableRel (ofUpper r).beats := fun i j =>
  inferInstanceAs
    (Decidable ((i < j ∧ (r i).testBit j = true) ∨ (j < i ∧ (r j).testBit i = false)))

/-- `ofUpper` with the row bitmasks given as a list: row `i` is `rows[i]` (`0` if missing). -/
def ofRows {n : ℕ} (rows : List ℕ) : Tournament (Fin n) :=
  ofUpper fun i => rows.getD i 0

instance decOfRows {n : ℕ} (rows : List ℕ) : DecidableRel (ofRows (n := n) rows).beats :=
  decOfUpper _

/-! ### Transitive subtournaments -/

/-- The transitive tournament `TT_k` on `Fin k`: `i` beats `j` iff `i < j`. -/
def TT (k : ℕ) : Tournament (Fin k) where
  beats i j := i < j
  irrefl i := lt_irrefl i
  asymm h := lt_asymm h
  total h := lt_or_gt_of_ne h

instance (k : ℕ) : DecidableRel (TT k).beats := fun i j => inferInstanceAs (Decidable (i < j))

/-- `T` contains a transitive subtournament on `k` vertices. -/
def ContainsTT (T : Tournament V) (k : ℕ) : Prop :=
  T.Contains (TT k)

/-- `T` contains no transitive subtournament on `k` vertices. -/
def TTFree (T : Tournament V) (k : ℕ) : Prop :=
  ¬ T.ContainsTT k

/-- `T` contains `TT_k` iff some `f : Fin k → V` has `f i` beating `f j` whenever `i < j`
(such an `f` is automatically injective). -/
theorem containsTT_iff {T : Tournament V} {k : ℕ} :
    T.ContainsTT k ↔ ∃ f : Fin k → V, ∀ i j, i < j → T.beats (f i) (f j) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e, fun i j h => e.map_rel_iff.2 h⟩
  · rintro ⟨f, hf⟩
    exact ⟨embOfHom (TT k) T f hf⟩

theorem ContainsTT.of_contains {T : Tournament V} {S : Tournament W} {k : ℕ}
    (hS : T.Contains S) (h : S.ContainsTT k) : T.ContainsTT k :=
  hS.trans h

theorem containsTT_of_comap {T : Tournament V} {f : W ↪ V} {k : ℕ}
    (h : (T.comap f).ContainsTT k) : T.ContainsTT k :=
  (T.contains_comap f).trans h

/-- Putting a vertex that beats every vertex of a chain in front of it gives a chain. -/
theorem chain_cons {T : Tournament V} {k : ℕ} {w : V} {f : Fin k → V}
    (hf : ∀ i j, i < j → T.beats (f i) (f j)) (hw : ∀ i, T.beats w (f i)) :
    ∀ i j, i < j →
      T.beats ((Fin.cons w f : Fin (k + 1) → V) i) ((Fin.cons w f : Fin (k + 1) → V) j) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j => simpa using hw j
  | succ i =>
    cases j using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ j => simpa using hf i j (Fin.succ_lt_succ_iff.1 hij)

/-- A vertex beating every vertex of a `TT_k` gives a `TT_(k+1)`. -/
theorem containsTT_cons {T : Tournament V} {k : ℕ} {w : V} {f : Fin k → V}
    (hf : ∀ i j, i < j → T.beats (f i) (f j)) (hw : ∀ i, T.beats w (f i)) :
    T.ContainsTT (k + 1) :=
  containsTT_iff.2 ⟨Fin.cons w f, chain_cons hf hw⟩

/-- A vertex beaten by every vertex of a `TT_k` gives a `TT_(k+1)`. -/
theorem containsTT_snoc {T : Tournament V} {k : ℕ} {w : V} {f : Fin k → V}
    (hf : ∀ i j, i < j → T.beats (f i) (f j)) (hw : ∀ i, T.beats (f i) w) :
    T.ContainsTT (k + 1) := by
  refine containsTT_iff.2 ⟨Fin.snoc f w, ?_⟩
  intro i j hij
  cases j using Fin.lastCases with
  | last =>
    cases i using Fin.lastCases with
    | last => exact absurd hij (lt_irrefl _)
    | cast i => simpa using hw i
  | cast j =>
    cases i using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last _))
    | cast i => simpa using hf i j (Fin.castSucc_lt_castSucc_iff.1 hij)

theorem containsTT_reverse {T : Tournament V} {k : ℕ} (h : T.ContainsTT k) :
    T.reverse.ContainsTT k := by
  obtain ⟨f, hf⟩ := containsTT_iff.1 h
  exact containsTT_iff.2 ⟨fun i => f i.rev, fun i j hij => hf _ _ (Fin.rev_lt_rev.2 hij)⟩

theorem reverse_reverse (T : Tournament V) : T.reverse.reverse = T := rfl

theorem containsTT_reverse_iff {T : Tournament V} {k : ℕ} :
    T.reverse.ContainsTT k ↔ T.ContainsTT k :=
  ⟨fun h => containsTT_reverse h, containsTT_reverse⟩

/-- A set of vertices is transitive if `beats` restricted to it is a transitive relation
(it is then a strict total order on the set, since `T` is a tournament). -/
def IsTransitiveSet (T : Tournament V) (S : Set V) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ∀ ⦃c⦄, c ∈ S → T.beats a b → T.beats b c → T.beats a c

/-! ### Neighbourhoods and degrees -/

/-- The in-neighbourhood `N⁻(v)`: the vertices that beat `v`. -/
def inNbhd (T : Tournament V) (v : V) : Set V := {u | T.beats u v}

/-- The out-neighbourhood `N⁺(v)`: the vertices that `v` beats. -/
def outNbhd (T : Tournament V) (v : V) : Set V := {u | T.beats v u}

section Degrees

variable [Fintype V]

open Classical in
/-- `N⁻(v)` as a `Finset`. -/
noncomputable def inFinset (T : Tournament V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => T.beats u v)

open Classical in
/-- `N⁺(v)` as a `Finset`. -/
noncomputable def outFinset (T : Tournament V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => T.beats v u)

/-- The in-degree `d⁻(v) = |N⁻(v)|`. -/
noncomputable def indeg (T : Tournament V) (v : V) : ℕ := (T.inFinset v).card

/-- The out-degree `d⁺(v) = |N⁺(v)|`. -/
noncomputable def outdeg (T : Tournament V) (v : V) : ℕ := (T.outFinset v).card

@[simp] theorem mem_inFinset {T : Tournament V} {u v : V} :
    u ∈ T.inFinset v ↔ T.beats u v := by
  simp [inFinset]

@[simp] theorem mem_outFinset {T : Tournament V} {u v : V} :
    u ∈ T.outFinset v ↔ T.beats v u := by
  simp [outFinset]

theorem coe_inFinset (T : Tournament V) (v : V) : (T.inFinset v : Set V) = T.inNbhd v := by
  ext u
  simp [inNbhd]

theorem coe_outFinset (T : Tournament V) (v : V) : (T.outFinset v : Set V) = T.outNbhd v := by
  ext u
  simp [outNbhd]

theorem inFinset_reverse (T : Tournament V) (v : V) : T.reverse.inFinset v = T.outFinset v := by
  ext u
  simp [reverse]

theorem indeg_reverse (T : Tournament V) (v : V) : T.reverse.indeg v = T.outdeg v := by
  simp [indeg, outdeg, inFinset_reverse]

/-- `d⁺(v) + d⁻(v) = |V| - 1`. -/
theorem outdeg_add_indeg (T : Tournament V) (v : V) :
    T.outdeg v + T.indeg v = Fintype.card V - 1 := by
  classical
  have hdisj : Disjoint (T.outFinset v) (T.inFinset v) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [mem_outFinset, mem_inFinset] at hu hu'
    exact T.asymm hu hu'
  have hunion : T.outFinset v ∪ T.inFinset v = Finset.univ.erase v := by
    ext u
    simp only [Finset.mem_union, mem_outFinset, mem_inFinset, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · rintro (h | h)
      · exact (T.ne_of_beats h).symm
      · exact T.ne_of_beats h
    · intro h
      exact T.total (Ne.symm h)
  unfold outdeg indeg
  rw [← Finset.card_union_of_disjoint hdisj, hunion,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

/-- `∑ d⁺ = ∑ d⁻`: both count the arcs. -/
theorem sum_outdeg_eq_sum_indeg (T : Tournament V) :
    ∑ v, T.outdeg v = ∑ v, T.indeg v := by
  classical
  simp only [outdeg, indeg, outFinset, inFinset, Finset.card_filter]
  exact Finset.sum_comm

/-- `2 ∑ d⁺ = |V| (|V| - 1)`. -/
theorem two_mul_sum_outdeg (T : Tournament V) :
    2 * ∑ v, T.outdeg v = Fintype.card V * (Fintype.card V - 1) := by
  have h : ∑ v, (T.outdeg v + T.indeg v) = Fintype.card V * (Fintype.card V - 1) := by
    simp [outdeg_add_indeg]
  rw [Finset.sum_add_distrib, ← sum_outdeg_eq_sum_indeg] at h
  omega

/-- Averaging: if `|V| ≥ 2m` with `m ≥ 1`, some vertex has out-degree at least `m`. -/
theorem exists_le_outdeg (T : Tournament V) (m : ℕ) (hm : 0 < m)
    (hV : 2 * m ≤ Fintype.card V) : ∃ v, m ≤ T.outdeg v := by
  by_contra hcon
  push Not at hcon
  have hle : ∑ v, T.outdeg v ≤ ∑ _v : V, (m - 1) :=
    Finset.sum_le_sum fun v _ => Nat.le_pred_of_lt (hcon v)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at hle
  have h2 := T.two_mul_sum_outdeg
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', hn'⟩ : ∃ n', Fintype.card V = n' + 1 := ⟨Fintype.card V - 1, by omega⟩
  rw [hn'] at h2 hle hV
  simp only [Nat.add_sub_cancel] at h2 hle
  nlinarith

end Degrees

/-- `k` vertices chosen from a finset of size at least `k`, as an embedding of `Fin k`. -/
theorem exists_embedding_of_le_card {s : Finset V} {k : ℕ} (h : k ≤ s.card) :
    ∃ g : Fin k ↪ V, ∀ i, g i ∈ s := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin k) (β := s)
    (by simpa using h)
  exact ⟨e.trans (Function.Embedding.subtype _), fun i => (e i).2⟩

/-! ### Transitive sets -/

section TransitiveSets

/-- A finite transitive set has a vertex beating all its other vertices. -/
theorem IsTransitiveSet.exists_source {T : Tournament V} {S : Finset V}
    (hS : T.IsTransitiveSet S) (hne : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, b ≠ a → T.beats a b := by
  classical
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image (fun x => (S.filter (T.beats x ·)).card) hne
  refine ⟨a, ha, fun b hb hba => ?_⟩
  rcases T.total hba with h | h
  · exfalso
    -- `b` beats `a`, hence everything that `a` beats, and `a` itself
    have hsub : insert a (S.filter (T.beats a ·)) ⊆ S.filter (T.beats b ·) := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_filter.2 ⟨ha, h⟩
      · obtain ⟨hxS, hax⟩ := Finset.mem_filter.1 hx
        exact Finset.mem_filter.2 ⟨hxS, hS hb ha hxS h hax⟩
    have hnot : a ∉ S.filter (T.beats a ·) := by
      simp [T.irrefl a]
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at this
    have := hmax b hb
    omega
  · exact h

/-- A transitive set of `k` vertices can be listed as a chain `Fin k → V`. -/
theorem IsTransitiveSet.exists_chain {T : Tournament V} :
    ∀ (k : ℕ) (S : Finset V), S.card = k → T.IsTransitiveSet S →
      ∃ f : Fin k → V, (∀ i j, i < j → T.beats (f i) (f j)) ∧ ∀ i, f i ∈ S
  | 0, _, _, _ => ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | k + 1, S, hcard, hS => by
    classical
    obtain ⟨a, ha, hsrc⟩ := hS.exists_source (Finset.card_pos.1 (by omega))
    have hS' : T.IsTransitiveSet (S.erase a : Set V) := fun x hx y hy z hz =>
      hS (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy)
        (Finset.mem_of_mem_erase hz)
    obtain ⟨f, hf, hfS⟩ := IsTransitiveSet.exists_chain k (S.erase a)
      (by rw [Finset.card_erase_of_mem ha]; omega) hS'
    refine ⟨Fin.cons a f, chain_cons hf fun i =>
      hsrc (f i) (Finset.mem_of_mem_erase (hfS i)) (Finset.ne_of_mem_erase (hfS i)), ?_⟩
    intro i
    cases i using Fin.cases with
    | zero => simpa using ha
    | succ i => simpa using Finset.mem_of_mem_erase (hfS i)

/-- `ContainsTT k` agrees with "some transitive set has `k` vertices". -/
theorem containsTT_iff_exists_transitive {T : Tournament V} {k : ℕ} :
    T.ContainsTT k ↔ ∃ S : Finset V, S.card = k ∧ T.IsTransitiveSet S := by
  constructor
  · rintro ⟨e⟩
    refine ⟨Finset.univ.map e.toEmbedding, by simp, ?_⟩
    intro a ha b hb c hc hab hbc
    simp only [Finset.coe_map, Set.mem_image, Finset.coe_univ, Set.mem_univ, true_and] at ha hb hc
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    obtain ⟨l, rfl⟩ := hc
    have hij : i < j := e.map_rel_iff.1 hab
    have hjl : j < l := e.map_rel_iff.1 hbc
    exact e.map_rel_iff.2 (show (TT k).beats i l from lt_trans hij hjl)
  · rintro ⟨S, hcard, hS⟩
    obtain ⟨f, hf, -⟩ := hS.exists_chain k S hcard
    exact containsTT_iff.2 ⟨f, hf⟩

end TransitiveSets

end Tournament

end R7
