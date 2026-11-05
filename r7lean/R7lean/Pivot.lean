import R7lean.Tournament

/-!
# Pivot instances

For tournaments `X` on `α` and `Z` on `β`, the pivot instance `X -p- Z` is the partial
tournament on `α ⊕ Unit ⊕ β` (`X`, then the pivot `p`, then `Z`) in which the arcs inside
`X` and inside `Z` are those of `X` and `Z`, every vertex of `X` beats `p`, `p` beats every
vertex of `Z`, and the `|X| |Z|` pairs between `X` and `Z` are free. A *completion* is a
tournament on `α ⊕ Unit ⊕ β` with these fixed arcs (`IsPivotCompletion`).

`HasTTFreeCompletion k X Z` says that some completion is `TT_k`-free; the SAT computations
of the project establish `¬ HasTTFreeCompletion 7 X Z` for 33 pairs `(X, Z)` (see
`R7lean/Facts.lean`).

Main results:
* `hasTTFreeCompletion_of_embeddings` (the sub-configuration lemma): if `T` is
  `TT_k`-free, `v` a vertex, and `X`, `Z` embed into `N⁻(v)` and `N⁺(v)`, then
  `X -p- Z` has a `TT_k`-free completion.
* `hasTTFreeCompletion_congr`: the question depends only on the isomorphism classes of
  `X` and `Z`.
-/

namespace R7

namespace Tournament

variable {α β α' β' V : Type*}

/-- The pivot vertex `p` of `α ⊕ Unit ⊕ β`. -/
def pivotVertex : α ⊕ Unit ⊕ β := .inr (.inl ())

/-- `C` is a completion of the pivot instance `X -p- Z`: it agrees with `X` on `α`, with
`Z` on `β`, every vertex of `α` beats the pivot and the pivot beats every vertex of `β`.
The arcs between `α` and `β` are arbitrary. -/
structure IsPivotCompletion (X : Tournament α) (Z : Tournament β)
    (C : Tournament (α ⊕ Unit ⊕ β)) : Prop where
  onX : ∀ a a', C.beats (.inl a) (.inl a') ↔ X.beats a a'
  onZ : ∀ b b', C.beats (.inr (.inr b)) (.inr (.inr b')) ↔ Z.beats b b'
  toPivot : ∀ a, C.beats (.inl a) pivotVertex
  fromPivot : ∀ b, C.beats pivotVertex (.inr (.inr b))

/-- The pivot instance `X -p- Z` has a `TT_k`-free completion. -/
def HasTTFreeCompletion (k : ℕ) (X : Tournament α) (Z : Tournament β) : Prop :=
  ∃ C : Tournament (α ⊕ Unit ⊕ β), IsPivotCompletion X Z C ∧ C.TTFree k

/-- The vertex map of a sub-configuration: `X` via `eX`, the pivot to `v`, `Z` via `eZ`. -/
def pivotMap (v : V) (eX : α → V) (eZ : β → V) : α ⊕ Unit ⊕ β → V
  | .inl a => eX a
  | .inr (.inl _) => v
  | .inr (.inr b) => eZ b

/-- **Sub-configuration lemma.** Let `T` be `TT_k`-free and `v` a vertex. If `X` embeds into
`T` inside `N⁻(v)` and `Z` embeds into `T` inside `N⁺(v)`, then `T` restricted to these
vertices and `v`, transported along the embeddings, is a `TT_k`-free completion of
`X -p- Z`. -/
theorem hasTTFreeCompletion_of_embeddings {X : Tournament α} {Z : Tournament β}
    (T : Tournament V) {k : ℕ} (hT : T.TTFree k) (v : V)
    (eX : X.beats ↪r T.beats) (hX : ∀ a, T.beats (eX a) v)
    (eZ : Z.beats ↪r T.beats) (hZ : ∀ b, T.beats v (eZ b)) :
    HasTTFreeCompletion k X Z := by
  have hinj : Function.Injective (pivotMap v eX eZ) := by
    rintro (a | ⟨⟨⟩⟩ | b) (a' | ⟨⟨⟩⟩ | b') h <;> simp only [pivotMap] at h
    · exact congrArg _ (eX.injective h)
    · exact absurd (h ▸ hX a) (T.irrefl v)
    · exact absurd (h ▸ hZ b') (T.asymm (hX a))
    · exact absurd (h ▸ hX a') (T.irrefl v)
    · rfl
    · exact absurd (h ▸ hZ b') (T.irrefl v)
    · exact absurd (h ▸ hX a') (T.asymm (hZ b))
    · exact absurd (h ▸ hZ b) (T.irrefl v)
    · exact congrArg _ (congrArg _ (eZ.injective h))
  refine ⟨T.comap ⟨pivotMap v eX eZ, hinj⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a a'
    exact eX.map_rel_iff
  · intro b b'
    exact eZ.map_rel_iff
  · intro a
    exact hX a
  · intro b
    exact hZ b
  · intro h
    exact hT (containsTT_of_comap h)

/-- Relabelling the three parts of `α ⊕ Unit ⊕ β`. -/
def pivotEquiv (eX : α ≃ α') (eZ : β ≃ β') : α ⊕ Unit ⊕ β ≃ α' ⊕ Unit ⊕ β' :=
  Equiv.sumCongr eX (Equiv.sumCongr (Equiv.refl Unit) eZ)

/-- Whether `X -p- Z` has a `TT_k`-free completion depends only on the isomorphism classes
of `X` and `Z`. (Used informally to identify NMH's labelled instance files with the
labelled tournaments of `R7lean/Data.lean`.) -/
theorem HasTTFreeCompletion.of_iso {k : ℕ} {X : Tournament α} {Z : Tournament β}
    {X' : Tournament α'} {Z' : Tournament β'}
    (iX : X.beats ≃r X'.beats) (iZ : Z.beats ≃r Z'.beats)
    (h : HasTTFreeCompletion k X Z) : HasTTFreeCompletion k X' Z' := by
  obtain ⟨C, hC, hfree⟩ := h
  let e := pivotEquiv iX.toEquiv iZ.toEquiv
  refine ⟨C.comap e.symm.toEmbedding, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a a'
    change C.beats (.inl (iX.symm a)) (.inl (iX.symm a')) ↔ _
    rw [hC.onX, iX.symm.map_rel_iff]
  · intro b b'
    change C.beats (.inr (.inr (iZ.symm b))) (.inr (.inr (iZ.symm b'))) ↔ _
    rw [hC.onZ, iZ.symm.map_rel_iff]
  · intro a
    exact hC.toPivot (iX.symm a)
  · intro b
    exact hC.fromPivot (iZ.symm b)
  · intro h'
    exact hfree (containsTT_of_comap h')

theorem hasTTFreeCompletion_congr {k : ℕ} {X : Tournament α} {Z : Tournament β}
    {X' : Tournament α'} {Z' : Tournament β'}
    (iX : X.beats ≃r X'.beats) (iZ : Z.beats ≃r Z'.beats) :
    HasTTFreeCompletion k X Z ↔ HasTTFreeCompletion k X' Z' :=
  ⟨HasTTFreeCompletion.of_iso iX iZ, HasTTFreeCompletion.of_iso iX.symm iZ.symm⟩

end Tournament

end R7
