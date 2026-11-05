import R7lean.Pivot
import R7lean.Enc.NMH
import R7lean.Enc.Tri
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

/-!
# Soundness of the CNF encodings

Everything here is proved in the kernel.

* `checkItem_sound`: a clause that passes the certified check of its item
  (`R7lean/Enc/Basic.lean`) is satisfied by the canonical assignment `tau ctx C` of every
  `TT_k`-free tournament `C` on `Fin ctx.n` that agrees with the fixed arcs (`Compat`):
  arc variables are read from `C`, 3-cycle variables say whether their triple is a 3-cycle
  in `C`. Hence `satisfiable_cnfOf`: `cnfOf ctx k items` is satisfiable, whatever the items.
* `compat_pivot`: a completion of `X -p- Z` (`R7lean/Pivot.lean`), relabelled to
  `Fin (a + 1 + b)`, agrees with the fixed arcs of the `PivotSpec`.
* `NMH.satisfiable_of_hasTTFreeCompletion`, `Tri.satisfiable_of_hasTTFreeCompletion`: the
  **soundness theorems** of the two encoders: `HasTTFreeCompletion 7 X Z → Satisfiable (cnf s)`
  for every pivot spec `s` whose arc functions describe `X` and `Z`.
* `ofRows_beats_iff`: `ofRows rows` and `upperArc rows` describe the same arcs; `isoOfPerm`:
  an explicit permutation checked by `decide` gives an isomorphism (used in
  `R7lean/NMHIso.lean`).

Note that nothing about the generators `NMH.items` and `Tri.items` is used: the theorems hold
for any list of items, because the CNF keeps only the items whose check passes.
-/

namespace R7

open Tournament

namespace Enc

/-! ### The canonical assignment -/

section Canonical

variable {n : ℕ}

open Classical in
/-- The arc `u → w` of `C` as a `Bool` (`false` outside the vertex range). -/
noncomputable def beatsB (C : Tournament (Fin n)) (u w : ℕ) : Bool :=
  if h : u < n ∧ w < n then decide (C.beats ⟨u, h.1⟩ ⟨w, h.2⟩) else false

/-- The orientation of the triple `a, b, c` in `C`. -/
noncomputable def oriC (C : Tournament (Fin n)) (a b c : ℕ) : Ori :=
  (beatsB C a b, beatsB C a c, beatsB C b c)

theorem beatsB_fin (C : Tournament (Fin n)) (x y : Fin n) :
    beatsB C x y = true ↔ C.beats x y := by
  simp [beatsB, x.2, y.2]

theorem beatsB_swap (C : Tournament (Fin n)) {u w : ℕ} (hu : u < n) (hw : w < n)
    (hne : u ≠ w) : beatsB C w u = !beatsB C u w := by
  have hne' : (⟨u, hu⟩ : Fin n) ≠ ⟨w, hw⟩ := fun h => hne (congrArg Fin.val h)
  simp only [beatsB, hu, hw, and_self, dite_true]
  rcases C.total hne' with h | h
  · simp [h, C.asymm h]
  · simp [h, C.asymm h]

end Canonical

/-- The canonical assignment of `C`: arc variables read from `C`, 3-cycle variables true iff
their triple is a 3-cycle in `C`. -/
noncomputable def tau (ctx : Ctx) (C : Tournament (Fin ctx.n)) (v : ℕ) : Bool :=
  match ctx.dec v with
  | .arc u w => beatsB C u w
  | .tri a b c => cyclicB (oriC C a b c)
  | .none => false

/-- `C` agrees with the fixed arcs of the context. -/
def Compat (ctx : Ctx) (C : Tournament (Fin ctx.n)) : Prop :=
  ∀ u w : Fin ctx.n, u ≠ w → ∀ b, ctx.fx u w = some b → (C.beats u w ↔ b = true)

section Sound

variable {ctx : Ctx} {C : Tournament (Fin ctx.n)}

theorem agree_of_compat (hC : Compat ctx C) {u w : ℕ} (hu : u < ctx.n) (hw : w < ctx.n)
    (hne : u ≠ w) : agree (ctx.fx u w) (beatsB C u w) = true := by
  cases h : ctx.fx u w with
  | none => rfl
  | some v =>
    have hne' : (⟨u, hu⟩ : Fin ctx.n) ≠ ⟨w, hw⟩ := fun h => hne (congrArg Fin.val h)
    have := hC ⟨u, hu⟩ ⟨w, hw⟩ hne' v h
    simp only [beatsB, hu, hw, and_self, dite_true, agree]
    cases v <;> simp_all

theorem locVal_oriC {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : c < ctx.n) {u w : ℕ}
    {v : Bool} (h : locVal a b c (oriC C a b c) u w = some v) : beatsB C u w = v := by
  have ha : a < ctx.n := by omega
  have hb : b < ctx.n := by omega
  unfold locVal oriC at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 <;> simp only [Bool.and_eq_true, beq_iff_eq] at * <;>
    obtain ⟨rfl, rfl⟩ := ‹_ ∧ _› <;> (try simp only [Option.some.injEq] at h) <;> subst h
  · rfl
  · exact beatsB_swap C ha hb (by omega)
  · rfl
  · exact beatsB_swap C ha hc (by omega)
  · rfl
  · exact beatsB_swap C hb hc (by omega)

theorem litLocal_sound {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : c < ctx.n) {l : ℤ}
    (h : litLocal ctx.dec a b c (oriC C a b c) l = true) : litHolds (tau ctx C) l = true := by
  unfold litLocal at h
  unfold litHolds tau
  split at h
  · next u w hdec =>
    rw [hdec]
    split at h
    · next v hv =>
      have := locVal_oriC hab hbc hc hv
      simp only [beq_iff_eq] at h
      subst h
      by_cases hl : 0 < l <;> simp [hl, this]
    · exact absurd h (by simp)
  · next a' b' c' hdec =>
    rw [hdec]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
    by_cases hl : 0 < l <;> simp_all
  · exact absurd h (by simp)

theorem mem_allOri (o : Ori) : o ∈ allOri := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [allOri]

theorem triOK_sound (hC : Compat ctx C) {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hc : c < ctx.n) {cl : List ℤ} {cyc : Bool} (h : triOK ctx a b c cl cyc = true)
    (hcyc : cyc = true → cyclicB (oriC C a b c) = true) :
    ∃ l ∈ cl, litHolds (tau ctx C) l = true := by
  unfold triOK at h
  have h' := List.all_eq_true.1 h (oriC C a b c) (mem_allOri _)
  have e1 := agree_of_compat hC (u := a) (w := b) (by omega) (by omega) (by omega)
  have e2 := agree_of_compat hC (u := a) (w := c) (by omega) hc (by omega)
  have e3 := agree_of_compat hC (u := b) (w := c) (by omega) hc (by omega)
  simp only [oriC] at h' hcyc
  rw [e1, e2, e3] at h'
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h'
  rcases Bool.or_eq_true_iff.1 h' with h'' | h''
  · cases cyc
    · simp at h''
    · simp [hcyc rfl] at h''
  · obtain ⟨l, hl, hl'⟩ := List.any_eq_true.1 h''
    exact ⟨l, hl, litLocal_sound hab hbc hc hl'⟩

/-! ### Triples of a sorted list -/

theorem allPairs_mem {g : ℕ → ℕ → Bool} :
    ∀ {S : List ℕ}, S.Pairwise (· < ·) → allPairs g S = true →
      ∀ {b c}, b ∈ S → c ∈ S → b < c → g b c = true
  | [], _, _, _, _, hb, _, _ => absurd hb (List.not_mem_nil)
  | x :: r, hS, h, b, c, hb, hc, hbc => by
    simp only [allPairs, Bool.and_eq_true, List.all_eq_true] at h
    rw [List.pairwise_cons] at hS
    rcases List.mem_cons.1 hb with hbx | hbr
    · rcases List.mem_cons.1 hc with hcx | hcr
      · omega
      · exact hbx ▸ h.1 c hcr
    · rcases List.mem_cons.1 hc with hcx | hcr
      · have := hS.1 b hbr; omega
      · exact allPairs_mem hS.2 h.2 hbr hcr hbc

theorem allTriples_mem {f : ℕ → ℕ → ℕ → Bool} :
    ∀ {S : List ℕ}, S.Pairwise (· < ·) → allTriples f S = true →
      ∀ {a b c}, a ∈ S → b ∈ S → c ∈ S → a < b → b < c → f a b c = true
  | [], _, _, _, _, _, ha, _, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: r, hS, h, a, b, c, ha, hb, hc, hab, hbc => by
    simp only [allTriples, Bool.and_eq_true] at h
    rw [List.pairwise_cons] at hS
    have hb' : b ∈ r := by
      rcases List.mem_cons.1 hb with hbx | hbr
      · rcases List.mem_cons.1 ha with hax | har
        · omega
        · have := hS.1 a har; omega
      · exact hbr
    have hc' : c ∈ r := by
      rcases List.mem_cons.1 hc with hcx | hcr
      · have := hS.1 b hb'; omega
      · exact hcr
    rcases List.mem_cons.1 ha with hax | har
    · exact hax ▸ allPairs_mem hS.2 h.1 hb' hc' hbc
    · exact allTriples_mem hS.2 h.2 har hb' hc' hab hbc

/-! ### A non-transitive set has a 3-cycle -/

/-- A 3-cycle `x → y → z → x` with `x < y < z`. -/
theorem cyclicB_of_cycle₁ {x y z : Fin ctx.n} (hxy : C.beats x y) (hyz : C.beats y z)
    (hzx : C.beats z x) : cyclicB (oriC C x y z) = true := by
  have h1 : beatsB C x y = true := (beatsB_fin C x y).2 hxy
  have h2 : beatsB C y z = true := (beatsB_fin C y z).2 hyz
  have h3 : beatsB C x z = false := by
    rw [← Bool.not_eq_true, beatsB_fin]; exact C.asymm hzx
  simp [oriC, cyclicB, h1, h2, h3]

/-- A 3-cycle `x → y → z → x`, listed as `x, z, y`. -/
theorem cyclicB_of_cycle₂ {x y z : Fin ctx.n} (hxy : C.beats x y) (hyz : C.beats y z)
    (hzx : C.beats z x) : cyclicB (oriC C x z y) = true := by
  have h1 : beatsB C x y = true := (beatsB_fin C x y).2 hxy
  have h2 : beatsB C z y = false := by
    rw [← Bool.not_eq_true, beatsB_fin]; exact C.asymm hyz
  have h3 : beatsB C x z = false := by
    rw [← Bool.not_eq_true, beatsB_fin]; exact C.asymm hzx
  simp [oriC, cyclicB, h1, h2, h3]

/-- A 3-cycle `x → y → z → x` whose smallest vertex is `x`. -/
theorem sorted_of_cycle_min {x y z : Fin ctx.n} (hxy : C.beats x y) (hyz : C.beats y z)
    (hzx : C.beats z x) (h1 : x.val < y.val) (h2 : x.val < z.val) :
    ∃ a b c : ℕ, (a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ (c = x ∨ c = y ∨ c = z) ∧
      a < b ∧ b < c ∧ cyclicB (oriC C a b c) = true := by
  rcases lt_trichotomy y.val z.val with h | h | h
  · exact ⟨x, y, z, by simp, by simp, by simp, h1, h, cyclicB_of_cycle₁ hxy hyz hzx⟩
  · exact absurd (Fin.ext h ▸ hyz) (C.irrefl z)
  · exact ⟨x, z, y, by simp, by simp, by simp, h2, h, cyclicB_of_cycle₂ hxy hyz hzx⟩

theorem or3_rot₁ {p q r : Prop} (h : q ∨ r ∨ p) : p ∨ q ∨ r := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl h

theorem or3_rot₂ {p q r : Prop} (h : r ∨ p ∨ q) : p ∨ q ∨ r := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Every 3-cycle, sorted. -/
theorem sorted_of_cycle {x y z : Fin ctx.n} (hxy : C.beats x y) (hyz : C.beats y z)
    (hzx : C.beats z x) :
    ∃ a b c : ℕ, (a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ (c = x ∨ c = y ∨ c = z) ∧
      a < b ∧ b < c ∧ cyclicB (oriC C a b c) = true := by
  have nxy : x.val ≠ y.val := fun h => C.irrefl x (by rwa [← Fin.ext h] at hxy)
  have nyz : y.val ≠ z.val := fun h => C.irrefl y (by rwa [← Fin.ext h] at hyz)
  have nzx : z.val ≠ x.val := fun h => C.irrefl z (by rwa [← Fin.ext h] at hzx)
  by_cases hA : x.val < y.val ∧ x.val < z.val
  · exact sorted_of_cycle_min hxy hyz hzx hA.1 hA.2
  by_cases hB : y.val < z.val ∧ y.val < x.val
  · obtain ⟨a, b, c, ha, hb, hc, h⟩ := sorted_of_cycle_min hyz hzx hxy hB.1 hB.2
    exact ⟨a, b, c, or3_rot₁ ha, or3_rot₁ hb, or3_rot₁ hc, h⟩
  have hC1 : z.val < x.val := by omega
  have hC2 : z.val < y.val := by omega
  obtain ⟨a, b, c, ha, hb, hc, h⟩ := sorted_of_cycle_min hzx hxy hyz hC1 hC2
  exact ⟨a, b, c, or3_rot₂ ha, or3_rot₂ hb, or3_rot₂ hc, h⟩

/-- If `C` is `TT_k`-free, every set of `k` vertices contains a 3-cycle of `C`. -/
theorem exists_cyclic_triple {k : ℕ} (hfree : C.TTFree k) {S : List ℕ} (hlen : S.length = k)
    (hlt : ∀ x ∈ S, x < ctx.n) (hS : S.Pairwise (· < ·)) :
    ∃ a b c : ℕ, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c ∧ cyclicB (oriC C a b c) = true := by
  classical
  let L : List (Fin ctx.n) := S.pmap (fun x hx => ⟨x, hx⟩) hlt
  have hmem : ∀ v : Fin ctx.n, v ∈ L ↔ v.val ∈ S := by
    intro v
    simp only [L, List.mem_pmap]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hv; exact ⟨v.val, hv, rfl⟩
  have hnd : L.Nodup := by
    refine List.Nodup.pmap (fun a _ b _ h => congrArg Fin.val h) ?_
    exact hS.imp (fun h => Nat.ne_of_lt h)
  have hcard : L.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup hnd, List.length_pmap, hlen]
  have hnt : ¬ C.IsTransitiveSet (L.toFinset : Set (Fin ctx.n)) := fun ht =>
    hfree (containsTT_iff_exists_transitive.2 ⟨L.toFinset, hcard, ht⟩)
  simp only [IsTransitiveSet, Finset.mem_coe, List.mem_toFinset, hmem, not_forall] at hnt
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz⟩ := hnt
  have hzx : C.beats z x := by
    have hne : x ≠ z := by
      rintro rfl
      exact C.asymm hxy hyz
    rcases C.total hne with h | h
    · exact absurd h hxz
    · exact h
  obtain ⟨a, b, c, ha, hb, hc, h⟩ := sorted_of_cycle hxy hyz hzx
  refine ⟨a, b, c, ?_, ?_, ?_, h⟩
  · rcases ha with rfl | rfl | rfl <;> assumption
  · rcases hb with rfl | rfl | rfl <;> assumption
  · rcases hc with rfl | rfl | rfl <;> assumption

/-! ### The checks are sound -/

theorem ksetOK_sound (hC : Compat ctx C) {k : ℕ} (hfree : C.TTFree k) {S : List ℕ}
    {cl : List ℤ} (h : ksetOK ctx k S cl = true) : ∃ l ∈ cl, litHolds (tau ctx C) l = true := by
  simp only [ksetOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hlt⟩, hS⟩, htri⟩ := h
  obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hcyc⟩ := exists_cyclic_triple hfree hlen hlt hS
  exact triOK_sound hC hab hbc (hlt c hc) (allTriples_mem hS htri ha hb hc hab hbc)
    (fun _ => hcyc)

theorem fixedOK_sound (hC : Compat ctx C) {cl : List ℤ} (h : fixedOK ctx cl = true) :
    ∃ l ∈ cl, litHolds (tau ctx C) l = true := by
  obtain ⟨l, hl, h⟩ := List.any_eq_true.1 h
  refine ⟨l, hl, ?_⟩
  split at h
  · next u w hdec =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hu, hw⟩, hne⟩, hfx⟩ := h
    have hne' : (⟨u, hu⟩ : Fin ctx.n) ≠ ⟨w, hw⟩ := fun h => hne (congrArg Fin.val h)
    have := hC ⟨u, hu⟩ ⟨w, hw⟩ hne' _ hfx
    unfold litHolds tau
    rw [hdec]
    simp only [beatsB, hu, hw, and_self, dite_true]
    by_cases hl : 0 < l <;> simp_all
  · exact absurd h (by simp)

theorem tdefOK_sound (hC : Compat ctx C) {a b c : ℕ} {cl : List ℤ}
    (h : tdefOK ctx a b c cl = true) : ∃ l ∈ cl, litHolds (tau ctx C) l = true := by
  simp only [tdefOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hab, hbc⟩, hc⟩, h⟩ := h
  exact triOK_sound hC hab hbc hc h (fun h => by simp at h)

/-- **Soundness of the checks.** -/
theorem checkItem_sound (hC : Compat ctx C) {k : ℕ} (hfree : C.TTFree k)
    {it : List ℤ × Just} (h : checkItem ctx k it = true) :
    ∃ l ∈ it.1, litHolds (tau ctx C) l = true := by
  rcases it with ⟨cl, _ | S | ⟨a, b, c⟩⟩
  · exact fixedOK_sound hC h
  · exact ksetOK_sound hC hfree h
  · exact tdefOK_sound hC h

/-- The CNF of any list of items is satisfied by `tau ctx C`, for every `TT_k`-free `C`
compatible with the fixed arcs. -/
theorem satisfiable_cnfOf (hC : Compat ctx C) {k : ℕ} (hfree : C.TTFree k)
    (items : List (List ℤ × Just)) : Satisfiable (cnfOf ctx k items) := by
  refine ⟨tau ctx C, ?_⟩
  intro cl hcl
  simp only [cnfOf, List.mem_map, List.mem_filter] at hcl
  obtain ⟨it, ⟨_, hit⟩, rfl⟩ := hcl
  exact checkItem_sound hC hfree hit

end Sound

/-! ### Pivot instances -/

/-- The vertices `0, …, a + b` as `Fin a ⊕ Unit ⊕ Fin b` (`X`, pivot `a`, `Z`). -/
def pivotFun (a b : ℕ) (i : Fin (a + 1 + b)) : Fin a ⊕ Unit ⊕ Fin b :=
  if h : i.val < a then .inl ⟨i, h⟩
  else if h' : i.val = a then .inr (.inl ())
  else .inr (.inr ⟨i - a - 1, by omega⟩)

/-- The inverse of `pivotFun`, as a number. -/
def pivotBack (a b : ℕ) : Fin a ⊕ Unit ⊕ Fin b → ℕ
  | .inl x => x
  | .inr (.inl _) => a
  | .inr (.inr y) => a + 1 + y

theorem pivotBack_fun (a b : ℕ) (i : Fin (a + 1 + b)) : pivotBack a b (pivotFun a b i) = i := by
  unfold pivotFun
  split_ifs with h1 h2
  · rfl
  · exact h2.symm
  · simp only [pivotBack]; omega

def pivotEmb (a b : ℕ) : Fin (a + 1 + b) ↪ Fin a ⊕ Unit ⊕ Fin b where
  toFun := pivotFun a b
  inj' := fun i j hij => Fin.ext (by rw [← pivotBack_fun a b i, ← pivotBack_fun a b j, hij])

theorem pivotEmb_lt {a b : ℕ} {i : Fin (a + 1 + b)} (h : i.val < a) :
    pivotEmb a b i = .inl ⟨i, h⟩ := by
  change pivotFun a b i = _
  simp [pivotFun, h]

theorem pivotEmb_eq {a b : ℕ} {i : Fin (a + 1 + b)} (h : i.val = a) :
    pivotEmb a b i = pivotVertex := by
  change pivotFun a b i = _
  simp [pivotFun, h, pivotVertex]

theorem pivotEmb_gt {a b : ℕ} {i : Fin (a + 1 + b)} (h : a < i.val) :
    pivotEmb a b i = .inr (.inr ⟨i - a - 1, by omega⟩) := by
  change pivotFun a b i = _
  simp [pivotFun, show ¬ i.val < a by omega, show i.val ≠ a by omega]

/-- A completion of `X -p- Z`, relabelled to `Fin (a + 1 + b)`, agrees with the fixed arcs of
the pivot spec. -/
theorem compat_pivot (s : PivotSpec) (dec : ℕ → VarMeaning) {X : Tournament (Fin s.a)}
    {Z : Tournament (Fin s.b)} (hX : ∀ i j : Fin s.a, X.beats i j ↔ s.xArc i j = true)
    (hZ : ∀ i j : Fin s.b, Z.beats i j ↔ s.zArc i j = true)
    {C' : Tournament (Fin s.a ⊕ Unit ⊕ Fin s.b)} (hC' : IsPivotCompletion X Z C') :
    Compat ⟨s.n, s.fx, dec⟩ (C'.comap (pivotEmb s.a s.b)) := by
  intro u w hne v hv
  have hne' : u.val ≠ w.val := fun h => hne (Fin.ext h)
  change C'.beats (pivotEmb s.a s.b u) (pivotEmb s.a s.b w) ↔ v = true
  simp only [PivotSpec.fx] at hv
  rcases lt_trichotomy u.val s.a with hu | hu | hu <;>
    rcases lt_trichotomy w.val s.a with hw | hw | hw
  · rw [pivotEmb_lt hu, pivotEmb_lt hw, hC'.onX, hX]
    simp only [hu, hw, ite_true, Option.some.injEq] at hv
    rw [hv]
  · rw [pivotEmb_lt hu, pivotEmb_eq hw]
    simp only [hu, hw, ite_true, lt_irrefl, ite_false, Option.some.injEq] at hv
    simp [← hv, hC'.toPivot]
  · simp [hu, show ¬ w.val < s.a by omega, show w.val ≠ s.a by omega] at hv
  · rw [pivotEmb_eq hu, pivotEmb_lt hw]
    simp only [hu, hw, lt_irrefl, ite_false, ite_true, Option.some.injEq] at hv
    simp [← hv, C'.asymm (hC'.toPivot _)]
  · omega
  · rw [pivotEmb_eq hu, pivotEmb_gt hw]
    simp only [hu, lt_irrefl, ite_false, ite_true, show ¬ w.val < s.a by omega,
      show w.val ≠ s.a by omega, Option.some.injEq] at hv
    simp [← hv, hC'.fromPivot]
  · simp [show ¬ u.val < s.a by omega, show u.val ≠ s.a by omega, hw] at hv
  · rw [pivotEmb_gt hu, pivotEmb_eq hw]
    simp only [show ¬ u.val < s.a by omega, show u.val ≠ s.a by omega, ite_false,
      lt_irrefl, hw, ite_true, Option.some.injEq] at hv
    simp [← hv, C'.asymm (hC'.fromPivot _)]
  · rw [pivotEmb_gt hu, pivotEmb_gt hw, hC'.onZ, hZ]
    simp only [show ¬ u.val < s.a by omega, show u.val ≠ s.a by omega,
      show ¬ w.val < s.a by omega, show w.val ≠ s.a by omega, ite_false,
      Option.some.injEq] at hv
    rw [hv]

/-- A pivot instance with a `TT_k`-free completion makes the CNF of any items satisfiable. -/
theorem satisfiable_of_pivot (s : PivotSpec) (dec : ℕ → VarMeaning) {k : ℕ}
    (items : List (List ℤ × Just)) {X : Tournament (Fin s.a)} {Z : Tournament (Fin s.b)}
    (hX : ∀ i j : Fin s.a, X.beats i j ↔ s.xArc i j = true)
    (hZ : ∀ i j : Fin s.b, Z.beats i j ↔ s.zArc i j = true)
    (h : HasTTFreeCompletion k X Z) : Satisfiable (cnfOf ⟨s.n, s.fx, dec⟩ k items) := by
  obtain ⟨C', hC', hfree⟩ := h
  exact satisfiable_cnfOf (compat_pivot s dec hX hZ hC') (fun h => hfree (containsTT_of_comap h))
    items

/-- **Soundness of the NMH encoding**: if `X -p- Z` has a TT₇-free completion, the CNF that
the Lean version of NMH's `tour-encode.c` produces for it is satisfiable. -/
theorem NMH.satisfiable_of_hasTTFreeCompletion (s : PivotSpec) {X : Tournament (Fin s.a)}
    {Z : Tournament (Fin s.b)} (hX : ∀ i j : Fin s.a, X.beats i j ↔ s.xArc i j = true)
    (hZ : ∀ i j : Fin s.b, Z.beats i j ↔ s.zArc i j = true)
    (h : HasTTFreeCompletion 7 X Z) : Satisfiable (NMH.cnf s) :=
  satisfiable_of_pivot s _ _ hX hZ h

/-- **Soundness of the 3-cycle encoding** (`src/encode.c`, `k = 7`, `limit = 1`). -/
theorem Tri.satisfiable_of_hasTTFreeCompletion (s : PivotSpec) {X : Tournament (Fin s.a)}
    {Z : Tournament (Fin s.b)} (hX : ∀ i j : Fin s.a, X.beats i j ↔ s.xArc i j = true)
    (hZ : ∀ i j : Fin s.b, Z.beats i j ↔ s.zArc i j = true)
    (h : HasTTFreeCompletion 7 X Z) : Satisfiable (Tri.cnf s) :=
  satisfiable_of_pivot s _ _ hX hZ h

/-! ### Row bitmasks and explicit isomorphisms -/

/-- `ofRows rows` has the arcs of `upperArc rows`. -/
theorem ofRows_beats_iff {n : ℕ} (rows : List ℕ) (i j : Fin n) :
    (ofRows (n := n) rows).beats i j ↔ upperArc rows i j = true := by
  simp only [ofRows, ofUpper, upperArc, Fin.lt_def]
  by_cases h : i.val < j.val
  · simp [h, Nat.lt_asymm h]
  · by_cases h' : j.val < i.val
    · simp [h, h']
    · simp [h, h']

/-- The arcs of `T` as a function on `ℕ`. -/
def refArc {n : ℕ} (T : Tournament (Fin n)) [DecidableRel T.beats] (i j : ℕ) : Bool :=
  if h : i < n ∧ j < n then decide (T.beats ⟨i, h.1⟩ ⟨j, h.2⟩) else false

/-- `perm` and `inv` are inverse permutations of `0..n-1` and `perm` maps the arcs of
`upperArc rows` to those of `ref`. -/
def checkIsoB (rows : List ℕ) (n : ℕ) (perm inv : List ℕ) (ref : ℕ → ℕ → Bool) : Bool :=
  (List.range n).all (fun i => decide (perm.getD i 0 < n) && decide (inv.getD i 0 < n) &&
    inv.getD (perm.getD i 0) 0 == i && perm.getD (inv.getD i 0) 0 == i) &&
  (List.range n).all (fun i => (List.range n).all (fun j =>
    upperArc rows i j == ref (perm.getD i 0) (perm.getD j 0)))

/-- The permutation `perm` is an isomorphism from `ofRows rows` onto `T` (checked by
`decide`). -/
def IsoOfPerm {n : ℕ} (rows perm inv : List ℕ) (T : Tournament (Fin n))
    [DecidableRel T.beats] : Prop :=
  checkIsoB rows n perm inv (refArc T) = true

instance {n : ℕ} (rows perm inv : List ℕ) (T : Tournament (Fin n)) [DecidableRel T.beats] :
    Decidable (IsoOfPerm rows perm inv T) :=
  inferInstanceAs (Decidable (_ = true))

/-- The isomorphism given by a checked permutation. -/
def isoOfPerm {n : ℕ} {rows perm inv : List ℕ} {T : Tournament (Fin n)} [DecidableRel T.beats]
    (h : IsoOfPerm rows perm inv T) : (ofRows (n := n) rows).beats ≃r T.beats :=
  have h1 : ∀ i < n, perm.getD i 0 < n ∧ inv.getD i 0 < n ∧
      inv.getD (perm.getD i 0) 0 = i ∧ perm.getD (inv.getD i 0) 0 = i := by
    intro i hi
    have := (List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).1) i (List.mem_range.2 hi)
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using this
  have h2 : ∀ i < n, ∀ j < n, upperArc rows i j = refArc T (perm.getD i 0) (perm.getD j 0) := by
    intro i hi j hj
    have := List.all_eq_true.1 ((List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2) i
      (List.mem_range.2 hi)) j (List.mem_range.2 hj)
    simpa using this
  { toFun := fun i => ⟨perm.getD i 0, (h1 i i.2).1⟩
    invFun := fun i => ⟨inv.getD i 0, (h1 i i.2).2.1⟩
    left_inv := fun i => Fin.ext (h1 i i.2).2.2.1
    right_inv := fun i => Fin.ext (h1 i i.2).2.2.2
    map_rel_iff' := by
      intro i j
      simp only [Equiv.coe_fn_mk]
      rw [ofRows_beats_iff, h2 i i.2 j j.2]
      unfold refArc
      split
      · exact decide_eq_true_iff.symm
      · next hneg => exact absurd (And.intro (h1 i i.2).1 (h1 j j.2).1) hneg }

end Enc

end R7
