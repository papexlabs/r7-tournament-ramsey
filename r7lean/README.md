# r7lean: Lean 4 formalization of the reduction for R(7) ≤ 46

Milestone 1 (5 Nov 2026). This Lean project proves

```lean
theorem R7.every_tournament_46_has_TT7 (T : Tournament (Fin 46)) : T.ContainsTT 7
```

(every tournament on 46 vertices contains a transitive subtournament on 7 vertices) from
13 axioms, each of which is exactly one computational fact established in this repository.
Everything else is proved: the reduction of `paper/r7le46.tex` §3, `R(6) ≤ 28`, the
20-vertex lemma, the sub-configuration lemma and the reversal step. There are **no `sorry`s**.

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build                              # the library (well under a minute with the Mathlib cache)
lake env lean CheckAxioms.lean          # #print axioms
lake env lean tools/CheckData.lean      # compares the Lean tournaments with ../data/*.txt
python3 -I tools/gen_data.py            # regenerates R7lean/Data.lean from ../data/
```

## Files

| File | Content |
|---|---|
| `R7lean/Tournament.lean` | `Tournament` (irreflexive, asymmetric, total `beats`), `Contains` (Mathlib relation embeddings `S.beats ↪r T.beats`; isomorphisms are `≃r`), `comap`, `induce`, `reverse`, `TT k`, `ContainsTT`, `TTFree`, `IsTransitiveSet` and `containsTT_iff_exists_transitive`, neighbourhoods `inFinset`/`outFinset`, degrees, `d⁺ + d⁻ = n − 1`, `2∑d⁺ = n(n−1)`, the averaging lemma `exists_le_outdeg`, `ofUpper`/`ofRows` (tournaments from matrix rows). |
| `R7lean/Data.lean` | **Generated** by `tools/gen_data.py`: `H6`, `W7`, `Y8`, `O21s`, `ST27`, `I24A..E`, `I23A..Y` from the matrices in `data/` (sha256 of each file in the doc comments); `ST26 = ST27 − {0}`, `ST25 = ST27 − {0,1}`; the families `I24 : Fin 5 → _`, `I23 : Fin 25 → _`. |
| `R7lean/Pivot.lean` | Pivot instances `X -p- Z` on `α ⊕ Unit ⊕ β`: `IsPivotCompletion`, `HasTTFreeCompletion k X Z`; the sub-configuration lemma `hasTTFreeCompletion_of_embeddings`; isomorphism invariance `hasTTFreeCompletion_congr`. |
| `R7lean/Facts.lean` | The 13 axioms (F2, F3, F5, F6, F7), each with the computation, files and sha256 values that justify it. |
| `R7lean/Lemma20.lean` | The 20-vertex lemma (TT₆, H₆ or W₇ in every tournament on ≥ 20 vertices), proved in full, including "a regular 5-tournament is RT₅". |
| `R7lean/Reduction.lean` | `R(5) ≤ 14` for any vertex type, `R(6) ≤ 28` (F1), the neighbourhood lemmas, the cases `d⁻(v) ≥ 28`, `26–27`, `25`, `24`, `23`, the reversal step, and the main theorem. |
| `CheckAxioms.lean` | `#print axioms` for the main theorem and the axiom-free lemmas. |
| `tools/gen_data.py`, `tools/CheckData.lean` | Generator for `Data.lean`, and a run-time check (Lean `#eval`, reading `../data/`) that every named tournament equals its matrix entry by entry, both triangles; `ST26`/`ST25` are checked against `ST27.txt` and against the `X` block of `data/ST26-p-TT5.txt`, and `TT 5` against its `Z` block. All 39 lines say `ok`. |

The named tournaments are explicit definitions, not opaque constants (the cheap option
was available: rows are stored as bitmasks, the tournament is read from the upper triangle,
as in `src/tourn.py`).

## `#print axioms`

Output of `lake env lean CheckAxioms.lean` on 5 Nov 2026:

```
'R7.every_tournament_46_has_TT7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 R7.R5_le_14,
 R7.pivot_I23_Y8,
 R7.pivot_I24_O21s,
 R7.pivot_ST25_H6,
 R7.pivot_ST25_W7,
 R7.pivot_ST26_TT5,
 R7.tt6free_21_contains_Y8_or_iso_O21s,
 R7.tt6free_22_contains_Y8,
 R7.tt6free_23_classes,
 R7.tt6free_24_classes,
 R7.tt6free_25_iso_ST25,
 R7.tt6free_26_iso_ST26]
'R7.Tournament.containsTT6_or_H6_or_W7' depends on axioms: [propext, Classical.choice, Quot.sound]
'R7.Tournament.hasTTFreeCompletion_of_embeddings' depends on axioms: [propext, Classical.choice, Quot.sound]
'R7.Tournament.hasTTFreeCompletion_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'R7.Tournament.containsTT_iff_exists_transitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool` (`native_decide` is not used).

## Axioms and what justifies them

All statements are about tournaments on `Fin n` (the weakest form; they are transported to
arbitrary vertex sets by embeddings in `Reduction.lean`). Full justification, file paths
and sha256 values are in the doc comments of `R7lean/Facts.lean`.

| Axiom | Statement | Justifying computation |
|---|---|---|
| `R5_le_14` (F2) | every tournament on `Fin 14` contains TT₅ | TT₅-free catalogue `scripts/a0_catalogue.py` (k = 5): `results/a0_k5.json` `"14": 0`, `data/tt5free/tt5free14.d6` empty; classical (Reid–Parker 1970). Not proof-checked (trust base T3). |
| `tt6free_26_iso_ST26` (F3) | TT₆-free on `Fin 26` ⇒ `≅ ST26` | certified enumeration `results/enum/k6n26/` (1 class) + `scripts/stage12_check.py` (= ST27 minus a vertex); also Sanchez-Flores. |
| `tt6free_25_iso_ST25` (F3) | TT₆-free on `Fin 25` ⇒ `≅ ST25` | `results/enum/k6n25/` + `stage12_check.py`; one class of 25-subsets of ST27 (`results/e1_catalog.json`). |
| `tt6free_24_classes` (F6) | TT₆-free on `Fin 24` ⇒ `≅ I24 i` for some `i : Fin 5` | `results/enum/k6n24/` + `stage12_check.py` (`equals_nmh`). |
| `tt6free_23_classes` (F6) | TT₆-free on `Fin 23` ⇒ `≅ I23 i` for some `i : Fin 25` | `results/enum/k6n23/` + `stage12_check.py` (`equals_nmh`). |
| `tt6free_22_contains_Y8` (F5, S22) | TT₆-free on `Fin 22` ⇒ contains `Y8` | `results/enum/k6n22/` + `stage12_check.py` (`without_Y8: 0`). |
| `tt6free_21_contains_Y8_or_iso_O21s` (F5, S21) | TT₆-free on `Fin 21` ⇒ contains `Y8` or `≅ O21s` | `results/enum/k6n21/` + `stage12_check.py` (`without_Y8_is_exactly_O21star`). |
| `pivot_ST26_TT5` (F7) | `ST26 -p- TT5` has no TT₇-free completion | Stage 4, `data/stage4_manifest.json` entry `ST26-p-TT5` (input `data/ST26-p-TT5.txt`, same labelling as here). |
| `pivot_ST25_H6` (F7) | `ST25 -p- H6` has no TT₇-free completion | Stage 4 entry `ST25-p-H6` (NMH's input; blocks isomorphic to ours). |
| `pivot_ST25_W7` (F7) | `ST25 -p- W7` has no TT₇-free completion | Stage 4 entry `ST25-p-W7`. |
| `pivot_I23_Y8` (F7) | `∀ i : Fin 25`, `I23 i -p- Y8` has no TT₇-free completion | Stage 4 entries `23A-p-Y8` … `23Y-p-Y8`. |
| `pivot_I24_O21s` (F7) | `∀ i : Fin 5`, `I24 i -p- O21s` has no TT₇-free completion | Stage 3, `data/stage3_manifest.json` (`24X-p-O21s`, built from `data/I24_X.txt` and `data/O21star.txt`, same labelling as here). |

F7 is stated semantically (`¬ HasTTFreeCompletion 7 X Z`: no TT₇-free tournament on
`X ⊕ Unit ⊕ Z` that agrees with `X` and `Z`, has the pivot beaten by all of `X` and beating
all of `Z`), not as a CNF statement.

Status of the certifying runs when the axioms were written: run 1 (`results/run1/`) did
every computation but its `lrat-check` did not check the final empty clause of each proof
(`notes/FEASIBILITY.md` §14); run 2 was in progress (`k6n23`–`k6n26` complete and certified,
`k6n22` running, `k6n21`, Stage 3 and Stage 4 not finished). The axioms are fully justified
once run 2 passes `stage12_check.py` (GO 1, GO 2, "ST26 unique: CERTIFIED") and every
Stage 3/4 summary says ALL CLOSED.

What is deliberately **not** an axiom:

* `R(6) ≤ 28` (F1) is proved from `R5_le_14` by the averaging argument
  (`containsTT6_of_card`).
* The 20-vertex lemma (F4) is proved (`Lemma20.lean`). The paper proves it by hand (NMH
  §5.2.2, `paper/r7le46.tex` Lemma `lem:h6g7`) and no computation in the repository checks
  it, so an axiom would not have been justified by a listed computation.
* The isomorphism invariance of pivot instances, used to pass from NMH's labelled input
  matrices to the labelled tournaments of `Data.lean`, is proved (`hasTTFreeCompletion_congr`);
  the isomorphisms themselves are the nauty canonical-form checks of
  `scripts/stage4_instances.py` (`X_iso_reference`, `Z_iso_reference`).

## Remaining `sorry`s

None.

## Next milestones

1. **Data.** Done in this milestone: the definitions are generated from `data/` and checked
   against the files by `tools/CheckData.lean`. Next: kernel-checked sanity facts by
   `decide` (e.g. `Y8` has 15 three-cycles, `O21s` is regular), as a guard against a
   misread file. A full kernel check that `ST26` is TT₆-free is probably too slow for `decide`.
2. **F7 ↔ CNF.** Formalize the TT₇-exclusion encodings (the direct encoding of NMH's
   `tour-encode` for Stage 4 and the 3-cycle encoding of `src/encode.c` for Stage 3) and
   prove soundness: a TT₇-free completion yields a satisfying assignment. Then either import
   the CNF and an LRAT proof into Lean, or state the axioms as "this CNF (sha256 …) is
   unsatisfiable" and prove `¬ HasTTFreeCompletion` from them. The Stage 3/4 proofs (thousands
   of solver-hours) are far too large to replay inside Lean, so the realistic target is the
   bridging lemma (Lean CNF ↔ the files, checked by `decide` or by a Lean-side generator and
   sha256) plus an external `cake_lpr`-checked certificate per cube, with the cube-cover
   check (`paper/r7le46.tex`, Lemma `lem:cover`) also formalized.
3. **F2–F6 ↔ enumeration.** Formalize the pivot decomposition (Proposition `prop:pivotdec`)
   and completeness (Proposition `prop:complete`), so that the catalogue axioms reduce to
   "each job formula plus its blocking clauses is UNSAT" and "each recorded model is
   isomorphic to a listed class" (the latter by explicit isomorphisms checked by `decide`
   instead of trusting `labelg`). `R5_le_14` stays computational (doubling from `R(4) ≤ 8`
   gives only `R(5) ≤ 16`); it could be certified by the same pivot enumeration from the
   TT₄-free lists (`data/tt4free/`).
