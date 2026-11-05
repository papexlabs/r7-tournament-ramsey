import R7lean.Data

/-!
# The 20-vertex lemma (NMH §5.2.2)

Every tournament on at least 20 vertices contains `TT₆`, `H₆` or `W₇` (`paper/r7le46.tex`,
Lemma `lem:h6g7`). This is a pen-and-paper lemma, proved here in full; it is not an axiom.

Proof. Some vertex `w` has out-degree `≥ 10`; inside `N⁺(w)` some vertex `v` beats `≥ 5`
others; take five of them. If one of the five, `u`, beats three others `p, q, r` of the
five, then `w, v, u` followed by `p, q, r` is a `TT₆` (if `{p, q, r}` is transitive) or an
`H₆ = TT₃ ⇒ C₃` (if it is a 3-cycle). Otherwise the five vertices induce a regular
tournament, which is the rotational tournament `RT₅` (`regular_five`), and `w, v` followed
by it is `W₇ = TT₂ ⇒ RT₅`.

The concrete `H6` and `W7` are the matrices of `data/H6.txt` and `data/W7.txt`
(`R7lean/Data.lean`); the arcs of both are read off by `decide`.
-/

namespace R7

namespace Tournament

variable {V : Type*}

/-- A regular tournament on five vertices is the rotational tournament `RT₅`: there is a
labelling `a, b, c, d, e` with `x → x+1, x+2` (indices mod 5). -/
theorem regular_five (R : Tournament (Fin 5)) (h : ∀ u, R.outdeg u ≤ 2) :
    ∃ a b c d e : Fin 5, R.beats a b ∧ R.beats a c ∧ R.beats b c ∧ R.beats b d ∧
      R.beats c d ∧ R.beats c e ∧ R.beats d e ∧ R.beats d a ∧ R.beats e a ∧ R.beats e b := by
  classical
  -- every out-degree is exactly 2, since the out-degrees sum to 10
  have h2 : ∀ u, R.outdeg u = 2 := by
    intro u
    by_contra hu
    have hlt : ∑ x, R.outdeg x < ∑ _x : Fin 5, 2 :=
      Finset.sum_lt_sum (fun x _ => h x) ⟨u, Finset.mem_univ _, lt_of_le_of_ne (h u) hu⟩
    have hsum := R.two_mul_sum_outdeg
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      at hlt hsum
    omega
  have h2' : ∀ u, R.indeg u = 2 := by
    intro u
    have := R.outdeg_add_indeg u
    rw [h2 u, Fintype.card_fin] at this
    omega
  -- a vertex beating at most one vertex is impossible
  have forced : ∀ x y : Fin 5, (∀ z, R.beats x z → z = y) → False := by
    intro x y hxy
    have hsub : R.outFinset x ⊆ {y} := by
      intro z hz
      rw [Finset.mem_singleton]
      exact hxy z (mem_outFinset.1 hz)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    have h2x := h2 x
    unfold outdeg at h2x
    omega
  -- the out- and in-neighbours of 0, ordered along their arc
  obtain ⟨b, c, h0b, h0c, hbc, hout0⟩ : ∃ b c, R.beats 0 b ∧ R.beats 0 c ∧ R.beats b c ∧
      ∀ z, R.beats 0 z → z = b ∨ z = c := by
    obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.1 (h2 0)
    have hmem : ∀ z, R.beats 0 z ↔ z = x ∨ z = y := by
      intro z
      rw [← mem_outFinset, hset, Finset.mem_insert, Finset.mem_singleton]
    rcases R.total hxy with hb | hb
    · exact ⟨x, y, (hmem x).2 (Or.inl rfl), (hmem y).2 (Or.inr rfl), hb,
        fun z hz => (hmem z).1 hz⟩
    · exact ⟨y, x, (hmem y).2 (Or.inr rfl), (hmem x).2 (Or.inl rfl), hb,
        fun z hz => ((hmem z).1 hz).symm⟩
  obtain ⟨d, e, hd0, he0, hde, hin0⟩ : ∃ d e, R.beats d 0 ∧ R.beats e 0 ∧ R.beats d e ∧
      ∀ z, R.beats z 0 → z = d ∨ z = e := by
    obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.1 (h2' 0)
    have hmem : ∀ z, R.beats z 0 ↔ z = x ∨ z = y := by
      intro z
      rw [← mem_inFinset, hset, Finset.mem_insert, Finset.mem_singleton]
    rcases R.total hxy with hb | hb
    · exact ⟨x, y, (hmem x).2 (Or.inl rfl), (hmem y).2 (Or.inr rfl), hb,
        fun z hz => (hmem z).1 hz⟩
    · exact ⟨y, x, (hmem y).2 (Or.inr rfl), (hmem x).2 (Or.inl rfl), hb,
        fun z hz => ((hmem z).1 hz).symm⟩
  have cover : ∀ z, z = 0 ∨ z = b ∨ z = c ∨ z = d ∨ z = e := by
    intro z
    by_cases hz : z = 0
    · exact Or.inl hz
    · rcases R.total (Ne.symm hz) with h' | h'
      · rcases hout0 z h' with h'' | h''
        · exact Or.inr (Or.inl h'')
        · exact Or.inr (Or.inr (Or.inl h''))
      · rcases hin0 z h' with h'' | h''
        · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h'')))
  -- the out-degree of `c`, `e`, `b` forces the remaining arcs
  have hcd : R.beats c d := by
    by_contra hn
    apply forced c e
    intro z hz
    rcases cover z with rfl | rfl | rfl | rfl | rfl
    · exact absurd hz (R.asymm h0c)
    · exact absurd hz (R.asymm hbc)
    · exact absurd hz (R.irrefl _)
    · exact absurd hz hn
    · rfl
  have hce : R.beats c e := by
    by_contra hn
    apply forced c d
    intro z hz
    rcases cover z with rfl | rfl | rfl | rfl | rfl
    · exact absurd hz (R.asymm h0c)
    · exact absurd hz (R.asymm hbc)
    · exact absurd hz (R.irrefl _)
    · rfl
    · exact absurd hz hn
  have heb : R.beats e b := by
    by_contra hn
    apply forced e 0
    intro z hz
    rcases cover z with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hz hn
    · exact absurd hz (R.asymm hce)
    · exact absurd hz (R.asymm hde)
    · exact absurd hz (R.irrefl _)
  have hbd : R.beats b d := by
    by_contra hn
    apply forced b c
    intro z hz
    rcases cover z with rfl | rfl | rfl | rfl | rfl
    · exact absurd hz (R.asymm h0b)
    · exact absurd hz (R.irrefl _)
    · rfl
    · exact absurd hz hn
    · exact absurd hz (R.asymm heb)
  exact ⟨0, b, c, d, e, h0b, h0c, hbc, hbd, hcd, hce, hde, hd0, he0, heb⟩

/-- `w, v, u` followed by a transitive triple `a → b → c` (with `a → c`) is a `TT₆`. -/
theorem containsTT6_of_six (T : Tournament V) {w v u a b c : V}
    (hwv : T.beats w v) (hwu : T.beats w u) (hwa : T.beats w a) (hwb : T.beats w b)
    (hwc : T.beats w c) (hvu : T.beats v u) (hva : T.beats v a) (hvb : T.beats v b)
    (hvc : T.beats v c) (hua : T.beats u a) (hub : T.beats u b) (huc : T.beats u c)
    (hab : T.beats a b) (hbc : T.beats b c) (hac : T.beats a c) : T.ContainsTT 6 := by
  refine containsTT_iff.2 ⟨![w, v, u, a, b, c], ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd hij (by decide)
    | assumption

/-- `w, v, u` followed by a 3-cycle `a → b → c → a` is an `H₆ = TT₃ ⇒ C₃`. -/
theorem containsH6_of_six (T : Tournament V) {w v u a b c : V}
    (hwv : T.beats w v) (hwu : T.beats w u) (hwa : T.beats w a) (hwb : T.beats w b)
    (hwc : T.beats w c) (hvu : T.beats v u) (hva : T.beats v a) (hvb : T.beats v b)
    (hvc : T.beats v c) (hua : T.beats u a) (hub : T.beats u b) (huc : T.beats u c)
    (hab : T.beats a b) (hbc : T.beats b c) (hca : T.beats c a) : T.Contains H6 := by
  refine ⟨embOfHom H6 T ![w, v, u, a, b, c] ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd hij (by decide)
    | assumption

/-- `w, v` followed by a rotational 5-tournament is a `W₇ = TT₂ ⇒ RT₅`. -/
theorem containsW7_of_seven (T : Tournament V) {w v a b c d e : V}
    (hwv : T.beats w v) (hwa : T.beats w a) (hwb : T.beats w b) (hwc : T.beats w c)
    (hwd : T.beats w d) (hwe : T.beats w e) (hva : T.beats v a) (hvb : T.beats v b)
    (hvc : T.beats v c) (hvd : T.beats v d) (hve : T.beats v e)
    (hab : T.beats a b) (hac : T.beats a c) (hbc : T.beats b c) (hbd : T.beats b d)
    (hcd : T.beats c d) (hce : T.beats c e) (hde : T.beats d e) (hda : T.beats d a)
    (hea : T.beats e a) (heb : T.beats e b) : T.Contains W7 := by
  refine ⟨embOfHom W7 T ![w, v, a, b, c, d, e] ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd hij (by decide)
    | assumption

/-- Three distinct vertices beaten by `w`, `v` and `u` (with `w → v → u`, `w → u`) give a
`TT₆` or an `H₆`. -/
theorem containsTT6_or_H6_of_three (T : Tournament V) {w v u p q r : V}
    (hwv : T.beats w v) (hwu : T.beats w u) (hvu : T.beats v u)
    (hwp : T.beats w p) (hwq : T.beats w q) (hwr : T.beats w r)
    (hvp : T.beats v p) (hvq : T.beats v q) (hvr : T.beats v r)
    (hup : T.beats u p) (huq : T.beats u q) (hur : T.beats u r)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) : T.ContainsTT 6 ∨ T.Contains H6 := by
  rcases T.total hpq with h1 | h1 <;> rcases T.total hqr with h2 | h2 <;>
    rcases T.total hpr with h3 | h3
  -- p → q, q → r
  · exact Or.inl (T.containsTT6_of_six hwv hwu hwp hwq hwr hvu hvp hvq hvr hup huq hur h1 h2 h3)
  · exact Or.inr (T.containsH6_of_six hwv hwu hwp hwq hwr hvu hvp hvq hvr hup huq hur h1 h2 h3)
  -- p → q, r → q
  · exact Or.inl (T.containsTT6_of_six hwv hwu hwp hwr hwq hvu hvp hvr hvq hup hur huq h3 h2 h1)
  · exact Or.inl (T.containsTT6_of_six hwv hwu hwr hwp hwq hvu hvr hvp hvq hur hup huq h3 h1 h2)
  -- q → p, q → r
  · exact Or.inl (T.containsTT6_of_six hwv hwu hwq hwp hwr hvu hvq hvp hvr huq hup hur h1 h3 h2)
  · exact Or.inl (T.containsTT6_of_six hwv hwu hwq hwr hwp hvu hvq hvr hvp huq hur hup h2 h3 h1)
  -- q → p, r → q
  · exact Or.inr (T.containsH6_of_six hwv hwu hwp hwr hwq hvu hvp hvr hvq hup hur huq h3 h2 h1)
  · exact Or.inl (T.containsTT6_of_six hwv hwu hwr hwq hwp hvu hvr hvq hvp hur huq hup h2 h1 h3)

/-- **The 20-vertex lemma** (NMH §5.2.2; `paper/r7le46.tex`, Lemma `lem:h6g7`): every
tournament on at least 20 vertices contains `TT₆`, `H₆` or `W₇`. -/
theorem containsTT6_or_H6_or_W7 [Fintype V] (T : Tournament V)
    (hV : 20 ≤ Fintype.card V) : T.ContainsTT 6 ∨ T.Contains H6 ∨ T.Contains W7 := by
  classical
  -- `w` with 10 out-neighbours `g 0, …, g 9`
  obtain ⟨w, hw⟩ := T.exists_le_outdeg 10 (by norm_num) (by omega)
  obtain ⟨g, hg⟩ := exists_embedding_of_le_card hw
  have hwg : ∀ i, T.beats w (g i) := fun i => mem_outFinset.1 (hg i)
  -- among them `g v` with 5 out-neighbours `g (h 0), …, g (h 4)` among the `g i`
  obtain ⟨v, hv⟩ := (T.comap g).exists_le_outdeg 5 (by norm_num) (by simp)
  obtain ⟨h, hh⟩ := exists_embedding_of_le_card hv
  have hvh : ∀ i, T.beats (g v) (g (h i)) := fun i => by
    have hi := mem_outFinset.1 (hh i)
    exact hi
  let R := (T.comap g).comap h
  have hR : ∀ i j, R.beats i j ↔ T.beats (g (h i)) (g (h j)) := fun _ _ => Iff.rfl
  by_cases hreg : ∀ u, R.outdeg u ≤ 2
  · -- the five vertices form `RT₅`
    obtain ⟨a, b, c, d, e, hab, hac, hbc, hbd, hcd, hce, hde, hda, hea, heb⟩ :=
      regular_five R hreg
    exact Or.inr (Or.inr (T.containsW7_of_seven (hwg v) (hwg _) (hwg _) (hwg _) (hwg _)
      (hwg _) (hvh a) (hvh b) (hvh c) (hvh d) (hvh e) hab hac hbc hbd hcd hce hde hda hea heb))
  · -- some `u` beats three of the five
    push Not at hreg
    obtain ⟨u, hu⟩ := hreg
    obtain ⟨k, hk⟩ := exists_embedding_of_le_card (s := R.outFinset u) (k := 3) hu
    have huk : ∀ i, T.beats (g (h u)) (g (h (k i))) := fun i => (hR _ _).1 (mem_outFinset.1 (hk i))
    have hne : ∀ i j : Fin 3, i ≠ j → g (h (k i)) ≠ g (h (k j)) := fun i j hij =>
      g.injective.ne (h.injective.ne (k.injective.ne hij))
    exact (T.containsTT6_or_H6_of_three (hwg v) (hwg _) (hvh u) (hwg _) (hwg _) (hwg _)
      (hvh _) (hvh _) (hvh _) (huk 0) (huk 1) (huk 2)
      (hne 0 1 (by decide)) (hne 1 2 (by decide)) (hne 0 2 (by decide))).imp_right Or.inl

end Tournament

end R7
