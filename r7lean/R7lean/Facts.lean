import R7lean.Data
import R7lean.Pivot

/-!
# The computational facts (axioms)

Each axiom below is exactly one fact established by a computation in this repository, and
nothing else. The named tournaments (`ST25`, `ST26`, `I23 i`, `I24 i`, `Y8`, `H6`, `W7`,
`O21s`) are explicit Lean definitions generated from the matrices in `data/` by
`tools/gen_data.py` (see `R7lean/Data.lean`, which records the sha256 of every source file);
`TT 5` is the transitive tournament on `Fin 5`. None of them is opaque; `tools/CheckData.lean`
compares each of them, entry by entry, with its matrix file.

Status of the certifying runs when this file was written (5 Nov 2026):
* run 1 (`results/run1/`, see its `README.md`) did every computation, but its `lrat-check`
  accepted an empty clause whose hints end without a conflict, so the last step of each
  proof was not checked (`notes/FEASIBILITY.md` §14);
* run 2 (patched checker) was in progress: `results/enum/k6n{23,24,25,26}` complete and
  certified (`summary.json` / `certify_summary.json`), `k6n22` running, `k6n21`, Stage 3
  (`results/stage3/`) and Stage 4 not finished. `scripts/stage12_check.py` must print
  GO 1, GO 2 and "ST26 unique: CERTIFIED" on the run-2 results, and every Stage 3/4
  `run/summary.json` must say ALL CLOSED, before these axioms are fully justified.

What is trusted besides the checked UNSAT proofs is listed in `paper/r7le46.tex`, §8
(Trust base); in particular nauty's `labelg` (equal canonical forms ⇒ isomorphic), the
TT₅-free lists, the encoders, and `lrat-check`.

Facts deliberately *not* stated as axioms:
* `R(6) ≤ 28` is proved from `R5_le_14` (`R7lean/Reduction.lean`, `containsTT6_of_card`);
* the 20-vertex lemma (every tournament on ≥ 20 vertices contains `TT₆`, `H₆` or `W₇`) has a
  pen-and-paper proof (NMH §5.2.2, `paper/r7le46.tex` Lemma `lem:h6g7`) and no computation in
  the repository checks it, so it is proved in `R7lean/Lemma20.lean`.
-/

namespace R7

open Tournament

/-! ### F2: `R(5) ≤ 14` -/

/-- **F2** (`R(5) ≤ 14`): every tournament on 14 vertices contains `TT₅`.

Classical (Reid–Parker 1970). Re-derived in this repository by the one-vertex extension
catalogue of TT₅-free tournaments (`scripts/a0_catalogue.py` with `k = 5`): the class counts for
`n = 1..14` are `1,1,2,4,11,35,121,376,692,369,45,1,1,0` (`results/a0_k5.json`, `"14": 0`),
and `data/tt5free/tt5free14.d6` is empty (sha256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). Cross-checked against
`gentourng` for `n ≤ 10` and NMH's TT₅-free files for `n ≤ 13`. Not certified by a proof
checker (trust base T3). -/
axiom R5_le_14 : ∀ T : Tournament (Fin 14), T.ContainsTT 5

/-! ### F3: uniqueness on 26 and 25 vertices -/

/-- **F3, n = 26**: every TT₆-free tournament on 26 vertices is isomorphic to `ST26`
(`ST27` minus a vertex).

Literature: Sanchez-Flores (1994/1998), cited by NMH §2. Computation: the certified
enumeration for `n = 26`, `results/enum/k6n26/` (1 job, 39 models, 1 class; run 2,
`summary.json` `all_complete`, `certify_summary.json` `all_jobs_verified`), and
`scripts/stage12_check.py` (`n = 26`: the single class equals every vertex-deleted
subtournament of `data/ST27.txt` by canonical form; output in `results/stage12_check.json`). -/
axiom tt6free_26_iso_ST26 :
    ∀ T : Tournament (Fin 26), T.TTFree 6 → Nonempty (ST26.beats ≃r T.beats)

/-- **F3, n = 25**: every TT₆-free tournament on 25 vertices is isomorphic to `ST25`.

Computation: certified enumeration `results/enum/k6n25/` (46 jobs, 1 class) and
`scripts/stage12_check.py` (`n = 25`: the class equals `ST27` restricted to vertices
`0..24`). `ST25` here is `ST27` restricted to vertices `2..26`; the two are isomorphic
because all 25-vertex subtournaments of `ST27` form one class (`scripts/e1_catalog.py`,
`results/e1_catalog.json`: `"sub_st27_25_classes": 1`). (Also NMH's classification.) -/
axiom tt6free_25_iso_ST25 :
    ∀ T : Tournament (Fin 25), T.TTFree 6 → Nonempty (ST25.beats ≃r T.beats)

/-! ### F6: the classifications on 24 and 23 vertices -/

/-- **F6, n = 24**: every TT₆-free tournament on 24 vertices is isomorphic to one of
`I24A, …, I24E` (`data/I24_{A..E}.txt`).

Computation: certified enumeration `results/enum/k6n24/` (414 jobs, 5 classes) and
`scripts/stage12_check.py` (`n = 24`, `equals_nmh`: the classes equal the canonical forms
of `data/I24_*.txt`). (Also NMH's classification.) -/
axiom tt6free_24_classes :
    ∀ T : Tournament (Fin 24), T.TTFree 6 → ∃ i : Fin 5, Nonempty ((I24 i).beats ≃r T.beats)

/-- **F6, n = 23**: every TT₆-free tournament on 23 vertices is isomorphic to one of
`I23A, …, I23Y` (`data/I23_{A..Y}.txt`).

Computation: certified enumeration `results/enum/k6n23/` (3,086 jobs, 25 classes) and
`scripts/stage12_check.py` (`n = 23`, `equals_nmh`: the classes equal the canonical forms
of `data/I23_*.txt`). (Also NMH's classification.) -/
axiom tt6free_23_classes :
    ∀ T : Tournament (Fin 23), T.TTFree 6 → ∃ i : Fin 25, Nonempty ((I23 i).beats ≃r T.beats)

/-! ### F5: `Y₈` in the catalogues on 22 and 21 vertices -/

/-- **F5, S22**: every TT₆-free tournament on 22 vertices contains `Y8` (`data/Y8.txt`).

Computation: certified enumeration `results/enum/k6n22/` (17,673 jobs, 89 classes) and
`scripts/stage12_check.py` (`n = 22`, `"without_Y8": 0`; containment by the backtracking
search `src/tourn.py`, `contains`). -/
axiom tt6free_22_contains_Y8 :
    ∀ T : Tournament (Fin 22), T.TTFree 6 → T.Contains Y8

/-- **F5, S21**: every TT₆-free tournament on 21 vertices contains `Y8` or is isomorphic to
`O21s` (`data/O21star.txt`).

Computation: certified enumeration `results/enum/k6n21/` (167,798 jobs, 17,040 classes) and
`scripts/stage12_check.py` (`n = 21`, `"without_Y8": 1` and
`"without_Y8_is_exactly_O21star": true`). -/
axiom tt6free_21_contains_Y8_or_iso_O21s :
    ∀ T : Tournament (Fin 21), T.TTFree 6 → T.Contains Y8 ∨ Nonempty (O21s.beats ≃r T.beats)

/-! ### F7: the pivot instances without a TT₇-free completion

Each axiom is the semantic content of one UNSAT result: no tournament on
`X ⊕ Unit ⊕ Z` extending `X` and `Z`, with the pivot beaten by all of `X` and beating all
of `Z`, is TT₇-free. The CNF files and their sha256 are pinned in `data/stage4_manifest.json`
(NMH's 28 instances, rebuilt with NMH's encoder `tour-encode`, re-solved with checked LRAT
proofs; results under `results/stage4/` (run 2) and `results/run1/stage4/`) and in
`data/stage3_manifest.json` (the five new instances; results under `results/stage3/` and
`results/run1/stage3/`). For each NMH instance, `scripts/stage4_instances.py verify` checked
that the input matrix is a pivot instance `X → p → Z` with exactly the `X × Z` pairs free,
that its `X` and `Z` blocks are isomorphic (by canonical form) to the tournaments named here
(`X_iso_reference`, `Z_iso_reference`), and that the CNF is sound for TT₇ exclusion
(`build/cnf_sound`: SOUND). The passage from NMH's labelling to ours is
`HasTTFreeCompletion.of_iso` (proved in `R7lean/Pivot.lean`).

Milestone 2: the main theorem no longer uses these five axioms. `R7lean/FactsCNF.lean` states
F7 as "this concrete CNF is unsatisfiable" and derives the five statements below from it
(`PivotFacts.ofCNF`); they are kept here for milestone 1's route
(`every_tournament_46_has_TT7_semantic`). -/

/-- **F7** `ST26 -p- TT5` has no TT₇-free completion.

Input `data/ST26-p-TT5.txt` (sha256
`211bcdc37118d40a1b66c0a981e92f31e914e698fed10f60df0731a3adef2197`), built by
`scripts/stage4_instances.py st26`: its `X` block is exactly `ST26` (= `ST27` minus vertex
`0`) and its `Z` block exactly `TT 5`, with the labelling used here. CNF
`cnf/stage4/ST26-p-TT5.cnf`, sha256
`fa91193c05eda98fc16b1019cdb12edce3c5d3395df327043fc0963c976dfb3b`. (NMH state this run but
published no input or log for it.) -/
axiom pivot_ST26_TT5 : ¬ HasTTFreeCompletion 7 ST26 (TT 5)

/-- **F7** `ST25 -p- H6` has no TT₇-free completion.

Input NMH `log25/ST25-p-H6.txt` (sha256
`5af4b7f863ee80f0166f2ac2610fd5f9e1230a715ed7969a3748d0c8eb6c613c`; its blocks are isomorphic
to `ST25` and `H6`). CNF `cnf/stage4/ST25-p-H6.cnf`, sha256
`2a4376a8419e20910caea75915e346fc55a1bbd02e7361b958d5dc62512f0093` (clause and byte counts
equal NMH's log). -/
axiom pivot_ST25_H6 : ¬ HasTTFreeCompletion 7 ST25 H6

/-- **F7** `ST25 -p- W7` has no TT₇-free completion.

Input NMH `log25/ST25-p-W7.txt` (sha256
`c76330e970a4a193c1db7c3a4fa311488f9f56c12c9fc35d918ac77fb0c524dc`; blocks isomorphic to
`ST25` and `W7`). CNF `cnf/stage4/ST25-p-W7.cnf`, sha256
`5b92889659ecd4cb55056a824b26d8e88aa803cc9dfbddb992ebc730f1036661`. -/
axiom pivot_ST25_W7 : ¬ HasTTFreeCompletion 7 ST25 W7

/-- **F7** `I23X -p- Y8` has no TT₇-free completion, for each of the 25 letters
(`I23 0 = I23A`, …, `I23 24 = I23Y`).

Inputs NMH `log23/23X-p-Y8.txt` (blocks isomorphic to `I23X` and `Y8`; the 25 `X` classes are
distinct, `"y8_x_classes_distinct": true`). CNFs `cnf/stage4/23X-p-Y8.cnf`, sha256:
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
axiom pivot_I23_Y8 : ∀ i : Fin 25, ¬ HasTTFreeCompletion 7 (I23 i) Y8

/-- **F7** `I24X -p- O21s` has no TT₇-free completion, for `X = A, …, E`
(`I24 0 = I24A`, …, `I24 4 = I24E`). These are the five new instances (Stage 3).

The instance matrices `cnf/24X-p-O21s.txt` were built by `src/instances.py` from
`data/I24_X.txt` and `data/O21star.txt` with the labelling used here (no isomorphism step);
CNFs `cnf/24X-p-O21s.tri.cnf` (encoder `build/encode`, 3-cycle mode, checked SOUND by
`build/tri_sound`), sha256 (`data/stage3_manifest.json`):
* A `b6a67cd97445f2ce7a5a37c56235158a5dd09f8512febcfc52788f9f054f6970`
* B `cb1402940fa2ab147762605fbd521f8fbe782c0627c35d437e0c8d8a75d5bdc1`
* C `8c53b09c90b032e087d88085247e5ad13c4d3c3cc25abec4b00f353af4dd738f`
* D `0facb5da175e9dd3162085f00fbfaf298e48da737299e42d04b5a5941af8397a`
* E `94489f5dd54b029e7a96fb545ba1d18cb170576d640ccb03a7800023ea681059` -/
axiom pivot_I24_O21s : ∀ i : Fin 5, ¬ HasTTFreeCompletion 7 (I24 i) O21s

end R7
