import R7lean.NMHIso

/-!
# F7 as statements about concrete CNFs

The pivot facts F7 of `R7lean/Facts.lean` (milestone 1) were stated semantically
(`¬ HasTTFreeCompletion 7 X Z`). Here they are replaced by five axioms saying that **concrete
CNFs are unsatisfiable**, and the semantic statements are derived from them in the kernel.

* The CNFs are Lean terms: `Enc.NMH.cnf s` (NMH's `tour-encode.c`, Stage 4) and `Enc.Tri.cnf s`
  (`src/encode.c` in 3-cycle mode, Stage 3), for the pivot specs `s` of
  `R7lean/Enc/Instances.lean`. Each is a list of DIMACS clauses (`R7lean/Enc/Basic.lean`).
* **Compiled run** (not kernel): `lake exe r7encode run NAME` evaluates the same Lean functions,
  writes the CNF in DIMACS format (header as in the manifest) and compares its sha256 with the
  manifest; a match means that the file proven unsatisfiable by the cube-and-conquer run is
  exactly this Lean CNF. Results of the runs are listed in `README.md`.
* **Kernel**: the soundness theorems `Enc.NMH.satisfiable_of_hasTTFreeCompletion` and
  `Enc.Tri.satisfiable_of_hasTTFreeCompletion` (`R7lean/EncSound.lean`), the isomorphisms
  between NMH's labelled `X` blocks and our `ST25`, `I23X` (`R7lean/NMHIso.lean`, by
  `decide`), and the derivations below.
* **External**: the unsatisfiability of each CNF, established by cube-and-conquer with every
  cube's LRAT proof checked (`paper/r7le46.tex` §7; the cube cover argument is
  `Enc.unsat_of_cover`, `R7lean/CubeCover.lean`). Results: Stage 4 `results/stage4/NAME/run/`
  (run 2) and `results/run1/stage4/NAME/` (run 1); Stage 3 `results/stage3/NAME/run/` (run 2) and
  `results/run1/stage3/NAME/` (run 1). Each axiom is justified once its run-2 `summary.json`
  says `ALL CLOSED` (run 1's `lrat-check` did not check the final empty clause,
  `notes/FEASIBILITY.md` §14).
-/

namespace R7

open Tournament Enc Enc.Inst

/-! ### The axioms -/

/-- **F7-CNF** `ST26-p-TT5`: the Lean NMH encoding of `ST26 -p- TT5` is unsatisfiable.

Its DIMACS file (header `p cnf 5456 1099282`) is `cnf/stage4/ST26-p-TT5.cnf`, sha256
`fa91193c05eda98fc16b1019cdb12edce3c5d3395df327043fc0963c976dfb3b`
(`data/stage4_manifest.json`; input `data/ST26-p-TT5.txt`). -/
axiom cnf_ST26_TT5_unsat : ¬ Satisfiable (NMH.cnf specST26_TT5)

/-- **F7-CNF** `ST25-p-H6` (NMH's input `log25/ST25-p-H6.txt`): unsatisfiable.

DIMACS file (header `p cnf 496 1687063`) `cnf/stage4/ST25-p-H6.cnf`, sha256
`2a4376a8419e20910caea75915e346fc55a1bbd02e7361b958d5dc62512f0093`. -/
axiom cnf_ST25_H6_unsat : ¬ Satisfiable (NMH.cnf specST25_H6)

/-- **F7-CNF** `ST25-p-W7` (NMH's input `log25/ST25-p-W7.txt`): unsatisfiable.

DIMACS file (header `p cnf 528 2603275`) `cnf/stage4/ST25-p-W7.cnf`, sha256
`5b92889659ecd4cb55056a824b26d8e88aa803cc9dfbddb992ebc730f1036661`. -/
axiom cnf_ST25_W7_unsat : ¬ Satisfiable (NMH.cnf specST25_W7)

/-- **F7-CNF** `23X-p-Y8`, `X = A, …, Y` (`i = 0, …, 24`; NMH's inputs `log23/23X-p-Y8.txt`):
unsatisfiable.

DIMACS files (header `p cnf 5456 C`) `cnf/stage4/23X-p-Y8.cnf`, sha256:
* A `fe1fb6a821aaa2871c1809f2425e19b4299ccc988a5defa2b0e86f055054636f`
* B `d71ad22bfe702570c99be74bf8a107932a44a6f8cfcbf0ea3e114f4b77b19481`
* C `91bf97ee7d97534f01e9908a8d333ffb8fd6d687b4b9eae09b3cf709511f9312`
* D `e9b59ad3b771d4218fc7d8430aea5305e223ef05e53a409cc545f51a2fd1bd25`
* E `ca24815c2f30afe0e16c7c78f6eb8bd28454f174ac8e84f6607dd46bce3618fb`
* F `b184585c0b4d6c61cc27dde7c882cf4560d6b707ae98bd49cc6abfc9f592b32e`
* G `6d24856dac70ae137a644edaf938e3f4a28f80fd07b0f08defa767f78e7706a8`
* H `a5030a5e4577b999f3d17c6dae7d4ab3ff3d4c6915405b67e0804e2f3103ffb4`
* I `212d48ec13cbdcdfedb86e128a4cac58535dbaf7969c5ce379332253ce0059b1`
* J `c0061227cc82079fc32965d5755fc3b30cc620e4251df681577865647bdfb3f9`
* K `757bac7849e73b1a99b40d37425f92f9f93d6d044576a0c587b106c754649f30`
* L `df0001f097bf5c66426fa01552310461dbef88ce0e8e50bdd9cc186f2283cb5c`
* M `62fb39b340083582258c6c0b024a449b95f7f688a238037ec259d979d31eb17c`
* N `dd73b2ce49bdf2274dcacc71e5f66bad5f7d6cd1994fe9707363040efeea3d94`
* O `2fdc7dd0d397ce6006c90260c236944c60df668e37f336b35d7fb8e4004d694a`
* P `38090a44dd5846b9348a693e99187281e2459603259e6b7bd80e54004a7c1e60`
* Q `de027f4cfadbb085b1b774280eee58cecae6a94ed25e516aca84e589ff7d32c6`
* R `a41d6a51c6ebd74729aa0f73c781c84bcfd3474e00cbf10636b5175761bef82e`
* S `ac2c79ff852f1b9ad2e1567498d8584a995eac783285a116d4b32b1e189253c3`
* T `8e33d799df9da5ba809ae36e21f78a6bf3dea3a942bd4535014406971d660839`
* U `fa08aafbcd6f7fb399831f4d04133e9924d3ff5b94df9e0c3a559b574e16d2c8`
* V `725b6bb2a37b125af28853b4ad93c54036cc46fb7679f108adc893b28aa678bc`
* W `6b2e6de60f0e8ca1a03f46186d10d5015b0d93dd4929b94ac8356d5293ee8af6`
* X `033d957315cc4fe8e9d6f1f5670b4e9ecc31e57b38717a44ca1c552a1d0c47a5`
* Y `bb8a6acf81964d3fa5f68c326b65e9c28651cd4569a86180433b114b47bbffff` -/
axiom cnf_23_Y8_unsat : ∀ i : Fin 25, ¬ Satisfiable (NMH.cnf (spec23_Y8 i))

/-- **F7-CNF** `24X-p-O21s`, `X = A, …, E` (`i = 0, …, 4`): the Lean 3-cycle encoding is
unsatisfiable.

DIMACS files (header `p cnf 11340 C`) `cnf/24X-p-O21s.tri.cnf`, sha256
(`data/stage3_manifest.json`):
* A `b6a67cd97445f2ce7a5a37c56235158a5dd09f8512febcfc52788f9f054f6970`
* B `cb1402940fa2ab147762605fbd521f8fbe782c0627c35d437e0c8d8a75d5bdc1`
* C `8c53b09c90b032e087d88085247e5ad13c4d3c3cc25abec4b00f353af4dd738f`
* D `0facb5da175e9dd3162085f00fbfaf298e48da737299e42d04b5a5941af8397a`
* E `94489f5dd54b029e7a96fb545ba1d18cb170576d640ccb03a7800023ea681059` -/
axiom cnf_24_O21s_unsat : ∀ i : Fin 5, ¬ Satisfiable (Tri.cnf (spec24_O21s i))

/-! ### The specs describe our tournaments -/

theorem ST27_eq_ofRows : ST27 = ofRows rowsST27 := rfl

theorem ST26_arc (i j : Fin 26) : ST26.beats i j ↔ specST26_TT5.xArc i j = true := by
  change ST27.beats i.succ j.succ ↔ upperArc rowsST27 (i + 1) (j + 1) = true
  rw [ST27_eq_ofRows, ofRows_beats_iff]
  rfl

theorem TT5_arc : ∀ i j : Fin 5, (TT 5).beats i j ↔ upperArc rowsTT5 i j = true := by
  decide

theorem I24_arc (i : Fin 5) (u w : Fin 24) :
    (I24 i).beats u w ↔ upperArc (rowsI24.getD i []) u w = true := by
  fin_cases i <;> exact ofRows_beats_iff _ u w

/-! ### F7, derived from the CNF axioms -/

theorem pivot_ST26_TT5_cnf : ¬ HasTTFreeCompletion 7 ST26 (TT 5) := fun h =>
  cnf_ST26_TT5_unsat (NMH.satisfiable_of_hasTTFreeCompletion specST26_TT5 ST26_arc TT5_arc h)

theorem pivot_ST25_H6_cnf : ¬ HasTTFreeCompletion 7 ST25 H6 := fun h =>
  cnf_ST25_H6_unsat (NMH.satisfiable_of_hasTTFreeCompletion specST25_H6
    (X := nmhST25_H6) (Z := H6) (ofRows_beats_iff _) (ofRows_beats_iff _)
    (h.of_iso isoST25_H6.symm (RelIso.refl _)))

theorem pivot_ST25_W7_cnf : ¬ HasTTFreeCompletion 7 ST25 W7 := fun h =>
  cnf_ST25_W7_unsat (NMH.satisfiable_of_hasTTFreeCompletion specST25_W7
    (X := nmhST25_W7) (Z := W7) (ofRows_beats_iff _) (ofRows_beats_iff _)
    (h.of_iso isoST25_W7.symm (RelIso.refl _)))

theorem pivot_I23_Y8_cnf (i : Fin 25) : ¬ HasTTFreeCompletion 7 (I23 i) Y8 := fun h => by
  obtain ⟨e⟩ := nmh23_iso i
  exact cnf_23_Y8_unsat i (NMH.satisfiable_of_hasTTFreeCompletion (spec23_Y8 i)
    (X := ofRows (rowsNMH23.getD i [])) (Z := Y8) (ofRows_beats_iff _) (ofRows_beats_iff _)
    (h.of_iso e.symm (RelIso.refl _)))

theorem pivot_I24_O21s_cnf (i : Fin 5) : ¬ HasTTFreeCompletion 7 (I24 i) O21s := fun h =>
  cnf_24_O21s_unsat i (Tri.satisfiable_of_hasTTFreeCompletion (spec24_O21s i)
    (Z := O21s) (I24_arc i) (ofRows_beats_iff _) h)

/-! ### The pivot facts used by the reduction -/

/-- The F7 facts used by the reduction (`R7lean/Reduction.lean`). -/
structure PivotFacts : Prop where
  st26_tt5 : ¬ HasTTFreeCompletion 7 ST26 (TT 5)
  st25_h6 : ¬ HasTTFreeCompletion 7 ST25 H6
  st25_w7 : ¬ HasTTFreeCompletion 7 ST25 W7
  i23_y8 : ∀ i : Fin 25, ¬ HasTTFreeCompletion 7 (I23 i) Y8
  i24_o21s : ∀ i : Fin 5, ¬ HasTTFreeCompletion 7 (I24 i) O21s

/-- The pivot facts from the CNF axioms. -/
theorem PivotFacts.ofCNF : PivotFacts :=
  ⟨pivot_ST26_TT5_cnf, pivot_ST25_H6_cnf, pivot_ST25_W7_cnf, pivot_I23_Y8_cnf,
    pivot_I24_O21s_cnf⟩

end R7
