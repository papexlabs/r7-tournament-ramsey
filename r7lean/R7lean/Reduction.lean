import R7lean.Facts
import R7lean.FactsCNF
import R7lean.Lemma20

/-!
# The reduction: every tournament on 46 vertices contains `TT₇`

`paper/r7le46.tex` §3. Let `T` be a TT₇-free tournament on 46 vertices and `v` a vertex; after
reversing `T` if necessary, `d⁻(v) ≥ 23`. Then
* `d⁻(v) ≥ 28` is impossible: `N⁻(v)` is TT₆-free and `R(6) ≤ 28` (`containsTT6_of_card`,
  from `R5_le_14` by the averaging argument);
* `d⁻(v) ∈ {26, 27}`: 26 vertices of `N⁻(v)` form `ST26`, and the `≥ 18` vertices of
  `N⁺(v)` contain `TT₅`; contradiction with `pivot_ST26_TT5`;
* `d⁻(v) = 25`: `N⁻(v) ≅ ST25`, and the 20 vertices of `N⁺(v)` contain `H₆` or `W₇`
  (the 20-vertex lemma); contradiction with `pivot_ST25_H6` / `pivot_ST25_W7`;
* `d⁻(v) = 24`: `N⁻(v) ≅ I24 i`. The 21 vertices of `N⁺(v)` contain `Y₈` (then 23 vertices of
  `N⁻(v)` form some `I23 j`; contradiction with `pivot_I23_Y8`) or form `O21*`
  (contradiction with `pivot_I24_O21s`);
* `d⁻(v) = 23`: `N⁻(v) ≅ I23 i`, and the 22 vertices of `N⁺(v)` contain `Y₈`;
  contradiction with `pivot_I23_Y8`.

Each contradiction is the sub-configuration lemma `hasTTFreeCompletion_of_embeddings`.

The pivot facts (F7) enter through `hP : PivotFacts` (`R7lean/FactsCNF.lean`). The main theorem
`every_tournament_46_has_TT7` uses `PivotFacts.ofCNF`, i.e. the CNF axioms of
`R7lean/FactsCNF.lean`; `every_tournament_46_has_TT7_semantic` is milestone 1's route, through
the semantic F7 axioms of `R7lean/Facts.lean` (kept for comparison).
-/

namespace R7

namespace Tournament

variable {V : Type*}

/-! ### Ramsey bounds -/

/-- `R(5) ≤ 14`, for any vertex type. -/
theorem containsTT5_of_card [Fintype V] (T : Tournament V) (h : 14 ≤ Fintype.card V) :
    T.ContainsTT 5 := by
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 14) (β := V) (by simpa using h)
  exact containsTT_of_comap (R5_le_14 (T.comap g))

/-- **F1**, `R(6) ≤ 28`: from `R(5) ≤ 14` by the averaging argument `R(k) ≤ 2 R(k-1)`. -/
theorem containsTT6_of_card [Fintype V] (T : Tournament V) (h : 28 ≤ Fintype.card V) :
    T.ContainsTT 6 := by
  classical
  obtain ⟨w, hw⟩ := T.exists_le_outdeg 14 (by norm_num) (by omega)
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card hw
  obtain ⟨f, hf⟩ := containsTT_iff.1 (R5_le_14 (T.comap g))
  exact containsTT_cons (f := fun i => g (f i)) hf (fun i => mem_outFinset.1 (hg (f i)))

/-! ### Neighbourhoods of a vertex of a TT₇-free tournament -/

/-- Vertices inside `N⁻(v)` of a `TT_(k+1)`-free tournament induce a `TT_k`-free one. -/
theorem ttFree_comap_of_beats_to {T : Tournament V} {k : ℕ} (hT : T.TTFree (k + 1))
    {W : Type*} (g : W ↪ V) {v : V} (hg : ∀ a, T.beats (g a) v) : (T.comap g).TTFree k := by
  intro h
  obtain ⟨f, hf⟩ := containsTT_iff.1 h
  exact hT (containsTT_snoc (f := fun i => g (f i)) hf (fun i => hg (f i)))

/-- Vertices inside `N⁺(v)` of a `TT_(k+1)`-free tournament induce a `TT_k`-free one. -/
theorem ttFree_comap_of_beats_from {T : Tournament V} {k : ℕ} (hT : T.TTFree (k + 1))
    {W : Type*} (g : W ↪ V) {v : V} (hg : ∀ a, T.beats v (g a)) : (T.comap g).TTFree k := by
  intro h
  obtain ⟨f, hf⟩ := containsTT_iff.1 h
  exact hT (containsTT_cons (f := fun i => g (f i)) hf (fun i => hg (f i)))

/-! ### The case analysis -/

section Cases

variable [Fintype V] {T : Tournament V} (hT : T.TTFree 7) (v : V)
include hT

/-- Some `n` vertices of `N⁻(v)` induce a copy of any tournament `X` that represents (via the
catalogue `hcat`) every TT₆-free tournament on `Fin n`. -/
theorem exists_emb_in_of_catalogue {n : ℕ} (hn : n ≤ T.indeg v) {ι : Type*}
    {α : ι → Type*} (X : ∀ i, Tournament (α i))
    (hcat : ∀ S : Tournament (Fin n), S.TTFree 6 → ∃ i, Nonempty ((X i).beats ≃r S.beats)) :
    ∃ i, ∃ e : (X i).beats ↪r T.beats, ∀ a, T.beats (e a) v := by
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card hn
  have hg' : ∀ a, T.beats (g a) v := fun a => mem_inFinset.1 (hg a)
  obtain ⟨i, ⟨iso⟩⟩ := hcat _ (ttFree_comap_of_beats_to hT g hg')
  exact ⟨i, iso.toRelEmbedding.trans (T.comapEmb g), fun a => hg' _⟩

/-- `d⁻(v) ≥ 28` is impossible (`R(6) ≤ 28`). -/
theorem indeg_lt_28 : T.indeg v < 28 := by
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card (k := 28) h
  exact ttFree_comap_of_beats_to hT g (fun a => mem_inFinset.1 (hg a))
    (containsTT6_of_card _ (by simp))

/-- `d⁻(v) ∈ {26, 27}` is impossible in a TT₇-free tournament on 46 vertices. -/
theorem indeg_not_26_27 (hP : PivotFacts) (hV : Fintype.card V = 46) (h26 : 26 ≤ T.indeg v)
    (h27 : T.indeg v ≤ 27) : False := by
  have hsum := T.outdeg_add_indeg v
  obtain ⟨-, eX, hX⟩ := exists_emb_in_of_catalogue hT v h26 (fun _ : Unit => ST26)
    (fun S hS => ⟨(), tt6free_26_iso_ST26 S hS⟩)
  -- `N⁺(v)` has at least 18 ≥ 14 vertices, so it contains `TT₅`
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card (s := T.outFinset v) (k := 14)
    (by unfold outdeg at hsum; omega)
  obtain ⟨eZ⟩ := R5_le_14 (T.comap g)
  exact hP.st26_tt5 (hasTTFreeCompletion_of_embeddings T hT v eX hX
    (eZ.trans (T.comapEmb g)) (fun b => mem_outFinset.1 (hg _)))

/-- `d⁻(v) = 25` is impossible in a TT₇-free tournament on 46 vertices. -/
theorem indeg_ne_25 (hP : PivotFacts) (hV : Fintype.card V = 46) (h25 : T.indeg v = 25) :
    False := by
  have hsum := T.outdeg_add_indeg v
  obtain ⟨-, eX, hX⟩ := exists_emb_in_of_catalogue hT v h25.ge (fun _ : Unit => ST25)
    (fun S hS => ⟨(), tt6free_25_iso_ST25 S hS⟩)
  -- `N⁺(v)` has 20 vertices: it contains `TT₆`, `H₆` or `W₇`
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card (s := T.outFinset v) (k := 20)
    (by unfold outdeg at hsum; omega)
  have hg' : ∀ a, T.beats v (g a) := fun a => mem_outFinset.1 (hg a)
  rcases (T.comap g).containsTT6_or_H6_or_W7 (by simp) with h6 | hH6 | hW7
  · exact ttFree_comap_of_beats_from hT g hg' h6
  · obtain ⟨eZ⟩ := hH6
    exact hP.st25_h6 (hasTTFreeCompletion_of_embeddings T hT v eX hX
      (eZ.trans (T.comapEmb g)) (fun b => hg' _))
  · obtain ⟨eZ⟩ := hW7
    exact hP.st25_w7 (hasTTFreeCompletion_of_embeddings T hT v eX hX
      (eZ.trans (T.comapEmb g)) (fun b => hg' _))

/-- If `N⁻(v)` has at least 23 vertices and `N⁺(v)` contains `Y₈`, contradiction. -/
theorem false_of_Y8_out (hP : PivotFacts) (h23 : 23 ≤ T.indeg v)
    (eZ : Y8.beats ↪r T.beats) (hZ : ∀ b, T.beats v (eZ b)) : False := by
  obtain ⟨i, eX, hX⟩ := exists_emb_in_of_catalogue hT v h23 I23 tt6free_23_classes
  exact hP.i23_y8 i (hasTTFreeCompletion_of_embeddings T hT v eX hX eZ hZ)

/-- `d⁻(v) = 24` is impossible in a TT₇-free tournament on 46 vertices. -/
theorem indeg_ne_24 (hP : PivotFacts) (hV : Fintype.card V = 46) (h24 : T.indeg v = 24) :
    False := by
  have hsum := T.outdeg_add_indeg v
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card (s := T.outFinset v) (k := 21)
    (by unfold outdeg at hsum; omega)
  have hg' : ∀ a, T.beats v (g a) := fun a => mem_outFinset.1 (hg a)
  rcases tt6free_21_contains_Y8_or_iso_O21s _ (ttFree_comap_of_beats_from hT g hg') with
    hY8 | hO21
  · -- `N⁺(v)` contains `Y₈`: use 23 vertices of `N⁻(v)`
    obtain ⟨eZ⟩ := hY8
    exact false_of_Y8_out hT v hP (by omega) (eZ.trans (T.comapEmb g)) (fun b => hg' _)
  · -- `N⁺(v) ≅ O21*`, and `N⁻(v) ≅ I24 i`
    obtain ⟨iZ⟩ := hO21
    obtain ⟨i, eX, hX⟩ := exists_emb_in_of_catalogue hT v h24.ge I24 tt6free_24_classes
    exact hP.i24_o21s i (hasTTFreeCompletion_of_embeddings T hT v eX hX
      (iZ.toRelEmbedding.trans (T.comapEmb g)) (fun b => hg' _))

/-- `d⁻(v) = 23` is impossible in a TT₇-free tournament on 46 vertices. -/
theorem indeg_ne_23 (hP : PivotFacts) (hV : Fintype.card V = 46) (h23 : T.indeg v = 23) :
    False := by
  have hsum := T.outdeg_add_indeg v
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card (s := T.outFinset v) (k := 22)
    (by unfold outdeg at hsum; omega)
  have hg' : ∀ a, T.beats v (g a) := fun a => mem_outFinset.1 (hg a)
  obtain ⟨eZ⟩ := tt6free_22_contains_Y8 _ (ttFree_comap_of_beats_from hT g hg')
  exact false_of_Y8_out hT v hP h23.ge (eZ.trans (T.comapEmb g)) (fun b => hg' _)

/-- In a TT₇-free tournament on 46 vertices every in-degree is at most 22. -/
theorem indeg_le_22 (hP : PivotFacts) (hV : Fintype.card V = 46) : T.indeg v ≤ 22 := by
  have h28 := indeg_lt_28 hT v
  by_contra h
  push Not at h
  rcases (by omega : (26 ≤ T.indeg v ∧ T.indeg v ≤ 27) ∨ T.indeg v = 25 ∨ T.indeg v = 24 ∨
      T.indeg v = 23) with h' | h' | h' | h'
  · exact indeg_not_26_27 hT v hP hV h'.1 h'.2
  · exact indeg_ne_25 hT v hP hV h'
  · exact indeg_ne_24 hT v hP hV h'
  · exact indeg_ne_23 hT v hP hV h'

end Cases

/-- No tournament on 46 vertices is TT₇-free. -/
theorem containsTT7_of_card_eq_46 (hP : PivotFacts) [Fintype V] (T : Tournament V)
    (hV : Fintype.card V = 46) :
    T.ContainsTT 7 := by
  classical
  by_contra hT
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨v⟩ := hne
  have hsum := T.outdeg_add_indeg v
  have hin := indeg_le_22 hT v hP hV
  -- in the reversal, `v` has in-degree `d⁺(v) ≥ 23`
  have hrev : T.reverse.TTFree 7 := fun h => hT (containsTT_reverse_iff.1 h)
  have hout := indeg_le_22 hrev v hP hV
  rw [indeg_reverse] at hout
  omega

end Tournament

open Tournament

/-- **Main theorem.** Every tournament on 46 vertices contains a transitive subtournament on
7 vertices: `R(7) ≤ 46`. -/
theorem every_tournament_46_has_TT7 (T : Tournament (Fin 46)) : T.ContainsTT 7 :=
  containsTT7_of_card_eq_46 PivotFacts.ofCNF T (Fintype.card_fin 46)

/-- The pivot facts from the semantic F7 axioms of milestone 1 (`R7lean/Facts.lean`). -/
theorem PivotFacts.ofSemantic : PivotFacts :=
  ⟨pivot_ST26_TT5, pivot_ST25_H6, pivot_ST25_W7, pivot_I23_Y8, pivot_I24_O21s⟩

/-- The main theorem by milestone 1's route (semantic F7 axioms), kept for comparison. -/
theorem every_tournament_46_has_TT7_semantic (T : Tournament (Fin 46)) : T.ContainsTT 7 :=
  containsTT7_of_card_eq_46 PivotFacts.ofSemantic T (Fintype.card_fin 46)

end R7
