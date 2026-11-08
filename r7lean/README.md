# r7lean: Lean 4 formalization of the reduction for R(7) ≤ 46

Milestone 2 (5 Nov 2026). This Lean project proves

```lean
theorem R7.every_tournament_46_has_TT7 (T : Tournament (Fin 46)) : T.ContainsTT 7
```

(every tournament on 46 vertices contains a transitive subtournament on 7 vertices) from
12 axioms, each of which is exactly one computational fact established in this repository:
the 7 catalogue facts F2–F6 of milestone 1, and **5 axioms saying that concrete CNFs are
unsatisfiable** (F7-CNF), which replace milestone 1's semantic pivot axioms. Everything else is
proved: the reduction of `paper/r7le46.tex` §3, `R(6) ≤ 28`, the 20-vertex lemma, the
sub-configuration lemma, the reversal step, and now the soundness of both TT₇-exclusion
encoders, the isomorphisms between NMH's labelled inputs and our tournaments, and the cube
cover lemma. There are **no `sorry`s** and no `native_decide`.

(Milestone 1's README said "13 axioms"; the list it printed has 12, with 5 F7 axioms covering
the 33 instances.)

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build                              # the library (well under a minute with the Mathlib cache)
lake env lean CheckAxioms.lean          # #print axioms
lake env lean tools/CheckData.lean      # compares the Lean tournaments with ../data/*.txt
python3 -I tools/gen_data.py            # regenerates R7lean/Data.lean from ../data/
python3 -I tools/gen_enc_data.py        # regenerates R7lean/Enc/Instances.lean, R7lean/NMHIso.lean
lake build r7encode                     # the executable (links no Mathlib)
nice -n 10 lake exe r7encode run 23A-p-Y8 --dir /tmp   # writes the CNF, compares its sha256
nice -n 10 lake exe r7encode run stage4                # all 28 Stage 4 instances (~8 min)
nice -n 10 lake exe r7encode run stage3                # the 5 Stage 3 instances (~2.5 min, 1 GB each)
```

## Files

| File | Content |
|---|---|
| `R7lean/Tournament.lean` | `Tournament` (irreflexive, asymmetric, total `beats`), `Contains` (Mathlib relation embeddings `S.beats ↪r T.beats`; isomorphisms are `≃r`), `comap`, `induce`, `reverse`, `TT k`, `ContainsTT`, `TTFree`, `IsTransitiveSet` and `containsTT_iff_exists_transitive`, neighbourhoods `inFinset`/`outFinset`, degrees, `d⁺ + d⁻ = n − 1`, `2∑d⁺ = n(n−1)`, the averaging lemma `exists_le_outdeg`, `ofUpper`/`ofRows` (tournaments from matrix rows). |
| `R7lean/Data.lean` | **Generated** by `tools/gen_data.py`: `H6`, `W7`, `Y8`, `O21s`, `ST27`, `I24A..E`, `I23A..Y` from the matrices in `data/` (sha256 of each file in the doc comments); `ST26 = ST27 − {0}`, `ST25 = ST27 − {0,1}`; the families `I24 : Fin 5 → _`, `I23 : Fin 25 → _`. |
| `R7lean/Pivot.lean` | Pivot instances `X -p- Z` on `α ⊕ Unit ⊕ β`: `IsPivotCompletion`, `HasTTFreeCompletion k X Z`; the sub-configuration lemma `hasTTFreeCompletion_of_embeddings`; isomorphism invariance `hasTTFreeCompletion_congr`. |
| `R7lean/Facts.lean` | Milestone 1's 12 axioms (F2, F3, F5, F6, F7), each with the computation, files and sha256 values that justify it. The 5 semantic F7 axioms are now used only by `every_tournament_46_has_TT7_semantic`. |
| `R7lean/Lemma20.lean` | The 20-vertex lemma (TT₆, H₆ or W₇ in every tournament on ≥ 20 vertices), proved in full. |
| `R7lean/Enc/Basic.lean` | *(no Mathlib)* DIMACS-level CNF model (`litHolds`, `Satisfiable` over `List (List Int)`), contexts (`Ctx`: fixed arcs and the meaning of each variable), the **certified clause checks** (`checkItem`: `.fixed`, `.kset S`, `.tri a b c`), `cnfOf`, the block driver `runBlocks`, `upperArc`, `PivotSpec`. |
| `R7lean/Enc/NMH.lean` | *(no Mathlib)* NMH's `tour-encode.c` with `limit = 5040` (Stage 4), reproduced: units, 7-sets in lexicographic order, Heap's algorithm (pruned, same order), the reduction loop of `printClause`; `NMH.cnf s`. |
| `R7lean/Enc/Tri.lean` | *(no Mathlib)* `src/encode.c` with `k = 7`, `limit = 1` (Stage 3), reproduced: prefix pruning by fixed 3-cycles, `ext_rec` up to two orderings, direct clause / 3-cycle clause, lazily numbered 3-cycle variables with their definition clauses, `cls_add` normalisation; `Tri.cnf s`. |
| `R7lean/Enc/Dimacs.lean` | *(no Mathlib)* `writeBlocks`/`writeCNF`: the loop of `runBlocks`, writing each checked clause in DIMACS format (streaming; the body goes to `<out>.body`, then the header and the body to `<out>`). |
| `R7lean/Enc/Instances.lean` | **Generated** by `tools/gen_enc_data.py`: raw rows of the tournaments, the `X` blocks of NMH's 27 input files, the 33 `PivotSpec`s, and the manifest data (sha256, clauses, bytes, header variables). |
| `R7lean/EncSound.lean` | **Soundness** (kernel): `checkItem_sound`, `satisfiable_cnfOf`, `compat_pivot`, `NMH.satisfiable_of_hasTTFreeCompletion`, `Tri.satisfiable_of_hasTTFreeCompletion`; `ofRows_beats_iff`; `IsoOfPerm`/`isoOfPerm` (an explicit permutation checked by `decide` gives an isomorphism). |
| `R7lean/NMHIso.lean` | **Generated**: NMH's labelled `X` blocks as tournaments, an explicit permutation onto `ST25` / `I23X` for each (found by backtracking in the generator), checked by `decide +kernel` (27 checks, a few seconds); `nmh23_iso`. Replaces the nauty canonical-form comparison of `scripts/stage4_instances.py` for these blocks. |
| `R7lean/FactsCNF.lean` | The 5 **F7-CNF axioms** `¬ Satisfiable (NMH.cnf …)` / `¬ Satisfiable (Tri.cnf …)` (manifest sha256 in the doc comments), the semantic F7 statements derived from them (`pivot_*_cnf`), and `PivotFacts` / `PivotFacts.ofCNF`. |
| `R7lean/CubeCover.lean` | The cube cover lemma (`paper/r7le46.tex`, Lemma `lem:cover`): `Closed F c` (leaf with `F ∧ c` unsatisfiable, or split into all `2^S` sign patterns), `unsat_of_cover`. |
| `R7lean/Reduction.lean` | `R(5) ≤ 14` for any vertex type, `R(6) ≤ 28` (F1), the neighbourhood lemmas, the cases `d⁻(v) ≥ 28`, `26–27`, `25`, `24`, `23` (parametrised by `hP : PivotFacts`), the reversal step, the main theorem (via `PivotFacts.ofCNF`) and `every_tournament_46_has_TT7_semantic` (milestone 1's route). |
| `R7Encode.lean` | The executable `r7encode` (`list`, `run NAME…`, and a test mode `matrix FILE B nmh\|tri OUT` for any pivot matrix file). |
| `CheckAxioms.lean` | `#print axioms`. |
| `tools/gen_data.py`, `tools/CheckData.lean` | Generator for `Data.lean` and its run-time check against `../data/` (milestone 1). |
| `tools/gen_enc_data.py` | Generator for `Enc/Instances.lean` and `NMHIso.lean`. It checks that each NMH input is the pivot instance `X → p → Z` with exactly the `X × Z` pairs free (both triangles), that its `Z` block equals our `Y8`/`H6`/`W7`, that `data/ST26-p-TT5.txt` is exactly `ST26 -p- TT5`, and that the input sha256 equal the manifest's. Nothing it produces is trusted: the rows enter the CNFs (so a wrong row changes the sha256) and the isomorphisms are re-checked by `decide`. |

## `#print axioms`

Output of `lake env lean CheckAxioms.lean` on 5 Nov 2026 (abridged to the first four):

```
'R7.every_tournament_46_has_TT7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 R7.R5_le_14,
 R7.cnf_23_Y8_unsat,
 R7.cnf_24_O21s_unsat,
 R7.cnf_ST25_H6_unsat,
 R7.cnf_ST25_W7_unsat,
 R7.cnf_ST26_TT5_unsat,
 R7.tt6free_21_contains_Y8_or_iso_O21s,
 R7.tt6free_22_contains_Y8,
 R7.tt6free_23_classes,
 R7.tt6free_24_classes,
 R7.tt6free_25_iso_ST25,
 R7.tt6free_26_iso_ST26]
'R7.every_tournament_46_has_TT7_semantic' depends on axioms: [propext,
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
'R7.PivotFacts.ofCNF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 R7.cnf_23_Y8_unsat,
 R7.cnf_24_O21s_unsat,
 R7.cnf_ST25_H6_unsat,
 R7.cnf_ST25_W7_unsat,
 R7.cnf_ST26_TT5_unsat]
'R7.Enc.NMH.satisfiable_of_hasTTFreeCompletion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`R7.Enc.Tri.satisfiable_of_hasTTFreeCompletion`, `R7.Enc.satisfiable_cnfOf`,
`R7.Enc.unsat_of_cover`, `R7.nmh23_iso`, `R7.isoST25_H6`, `R7.isoST25_W7` and milestone 1's
lemmas depend on `[propext, Classical.choice, Quot.sound]` only. No `sorryAx`, no
`Lean.ofReduceBool`.

## Axioms and what justifies them

### F2–F6 (unchanged from milestone 1)

All statements are about tournaments on `Fin n`. Full justification in `R7lean/Facts.lean`.

| Axiom | Statement | Justifying computation |
|---|---|---|
| `R5_le_14` (F2) | every tournament on `Fin 14` contains TT₅ | TT₅-free catalogue `scripts/a0_catalogue.py` (k = 5): `results/a0_k5.json` `"14": 0`, `data/tt5free/tt5free14.d6` empty; classical (Reid–Parker 1970). Not proof-checked (trust base T3). |
| `tt6free_26_iso_ST26` (F3) | TT₆-free on `Fin 26` ⇒ `≅ ST26` | certified enumeration `results/enum/k6n26/` (1 class) + `scripts/stage12_check.py`; also Sanchez-Flores. |
| `tt6free_25_iso_ST25` (F3) | TT₆-free on `Fin 25` ⇒ `≅ ST25` | `results/enum/k6n25/` + `stage12_check.py`; `results/e1_catalog.json`. |
| `tt6free_24_classes` (F6) | TT₆-free on `Fin 24` ⇒ `≅ I24 i` for some `i : Fin 5` | `results/enum/k6n24/` + `stage12_check.py` (`equals_nmh`). |
| `tt6free_23_classes` (F6) | TT₆-free on `Fin 23` ⇒ `≅ I23 i` for some `i : Fin 25` | `results/enum/k6n23/` + `stage12_check.py` (`equals_nmh`). |
| `tt6free_22_contains_Y8` (F5, S22) | TT₆-free on `Fin 22` ⇒ contains `Y8` | `results/enum/k6n22/` + `stage12_check.py` (`without_Y8: 0`). |
| `tt6free_21_contains_Y8_or_iso_O21s` (F5, S21) | TT₆-free on `Fin 21` ⇒ contains `Y8` or `≅ O21s` | `results/enum/k6n21/` + `stage12_check.py` (`without_Y8_is_exactly_O21star`). |

### F7-CNF (new)

| Axiom | Statement | DIMACS file (sha256 in the doc comment and the manifest) |
|---|---|---|
| `cnf_ST26_TT5_unsat` | `¬ Satisfiable (NMH.cnf specST26_TT5)` | `cnf/stage4/ST26-p-TT5.cnf`, `data/stage4_manifest.json` |
| `cnf_ST25_H6_unsat` | `¬ Satisfiable (NMH.cnf specST25_H6)` | `cnf/stage4/ST25-p-H6.cnf` |
| `cnf_ST25_W7_unsat` | `¬ Satisfiable (NMH.cnf specST25_W7)` | `cnf/stage4/ST25-p-W7.cnf` |
| `cnf_23_Y8_unsat` | `∀ i : Fin 25, ¬ Satisfiable (NMH.cnf (spec23_Y8 i))` | `cnf/stage4/23X-p-Y8.cnf`, `X = A..Y` |
| `cnf_24_O21s_unsat` | `∀ i : Fin 5, ¬ Satisfiable (Tri.cnf (spec24_O21s i))` | `cnf/24X-p-O21s.tri.cnf`, `X = A..E`, `data/stage3_manifest.json` |

From them, `R7lean/FactsCNF.lean` proves the semantic statements of milestone 1
(`pivot_ST26_TT5_cnf`, …, `pivot_I24_O21s_cnf`), with the soundness theorems and, for NMH's
labelled inputs (`ST25-p-H6`, `ST25-p-W7`, `23X-p-Y8`), the kernel-checked isomorphisms of
`R7lean/NMHIso.lean` (`23W` and `23X` are literally our `I23W`, `I23X`; the other 25 blocks are
relabellings). `data/ST26-p-TT5.txt` and the Stage 3 matrices use our labelling, so no
isomorphism is needed there.

### What is proved in the kernel, what is a compiled run, what is external

**Kernel** (`#print axioms` above):
* the encoders' soundness: for every pivot spec `s` whose arc functions describe `X` and `Z`,
  `HasTTFreeCompletion 7 X Z → Satisfiable (NMH.cnf s)` and the same for `Tri.cnf s`. The proof
  does not look at the generators: `cnf = cnfOf ctx 7 items` keeps only the items that pass a
  certified local check, and `checkItem_sound` shows that every such clause is satisfied by the
  canonical assignment of a TT₇-free completion (arc variables read from the completion,
  3-cycle variables true iff their triple is a 3-cycle). For a `.kset S` item the check says that
  every 3-cycle orientation of every triple of `S` consistent with the fixed arcs makes some
  literal true; this covers NMH's reduced clauses, the direct clauses and the 3-cycle clauses of
  `src/encode.c`. The 3-cycle definitions are `.tri` items (true under every orientation), the
  units are `.fixed` items;
* the specs describe our tournaments (`ofRows_beats_iff`, `ST26_arc`, `TT5_arc`, `I24_arc`), and
  NMH's labelled `X` blocks are isomorphic to `ST25` / `I23X` (`decide +kernel` on explicit
  permutations);
* the derivation of F7 from the CNF axioms, and the reduction;
* the cube cover lemma `unsat_of_cover` (general; it is not applied to the actual cube trees yet).

**Compiled run** (`lake exe r7encode`): that the Lean terms `NMH.cnf s` / `Tri.cnf s` are, clause
for clause, the DIMACS files of the manifests. The executable evaluates the very functions that
define the CNFs (`NMH.env`/`NMH.step`, `Tri.env`/`Tri.final`/`Tri.step`, `checkItem`, the
contexts) in the loop of `runBlocks`, writes the clauses that pass the checks, and compares
sha256 (via `shasum -a 256`), clause count and byte count with the manifest, and reports the
number of items that failed a check. Trusted here: the Lean compiler and runtime, the ~80-line
writer `R7lean/Enc/Dimacs.lean` (its loop mirrors `runBlocks`; not proved), and `shasum`.
A wrong row, a wrong generator or a wrong writer shows up as a sha256 mismatch.

**External**: the unsatisfiability of the 33 DIMACS files, by cube-and-conquer
(`paper/r7le46.tex` §7): every cube `F ∧ c` refuted by CaDiCaL with its LRAT proof checked
while it is solved by the patched `lrat-check`; in run 2 every LRAT proof of the enumeration, of Stage 3 and of Stage 4 is also checked by the
formally verified `cake_lpr` (during the run, or by re-solving afterwards; `notes/RUN2.md`); the level-0 cover formula has its own checked LRAT
proof, and `scripts/cnc_summary.py` checks the split structure and prints `ALL CLOSED`
(conditions (1)–(3) of `unsat_of_cover`). Results: Stage 4 `results/stage4/NAME/run/` (run 2),
`results/run1/stage4/` (run 1); Stage 3 `results/stage3/NAME/run/` (run 2),
`results/run1/stage3/` (run 1). Run 1's `lrat-check` did not check the final empty clause
(`notes/FEASIBILITY.md` §14), so each F7-CNF axiom is justified once the run-2 summary of its
instances says `ALL CLOSED`. When this milestone was written, run 2 of Stage 3 was in progress
(no `summary.json` yet) and the run-2 Stage 4 results were not in this checkout. Run 2 has since finished (8 Nov 2026): all 33 run-2 summaries say `ALL CLOSED`, and every leaf was checked by both checkers (`notes/RUN2.md`).

## The executable runs

`lake exe r7encode run NAME` (one process per instance, `nice -n 10`, on the development Mac,
5 Nov 2026; files written to a scratch directory and deleted after hashing). **All 33 CNFs
produced by the Lean encoders have exactly the manifest's sha256, clause count and byte count,
and no generated item failed a certified check.**

| Instances | Encoder | sha256 | Clauses / bytes | Failed checks | Time, max RSS (each) |
|---|---|---|---|---|---|
| `ST26-p-TT5`, `ST25-p-H6`, `ST25-p-W7` | NMH | 3/3 MATCH | 1.10M–2.60M / 48–116 MB, all equal to the manifest | 0 | 7–18 s, ≤ 24 MB |
| `23A-p-Y8` … `23Y-p-Y8` | NMH | 25/25 MATCH | 2.20M–2.36M / 98–106 MB, all equal | 0 | 15–17 s, ≤ 28 MB |
| `24A-p-O21s` … `24E-p-O21s` | `encode.c`, `limit = 1` | 5/5 MATCH | 8.99M–9.01M / 1.07 GB, all equal | 0 | 149–169 s (two passes), ≤ 208 MB |

The NMH encoder in Lean is slightly faster than the C program (16 s against 20 s for
`23A-p-Y8`, where the C program reaches 642 MB RSS because it never frees its per-permutation
buffers). Stage 3 takes two passes (the first fixes the numbering of the 3-cycle variables, which
the context of the checks needs).

## The encoders, and what reproducing them showed

Both encoders are reproduced exactly (same variable numbering, clause order and literal
order); the Lean code is unverified and only has to produce the same bytes. Before the full
runs, both were compared with the C programs on five random pivot instances (`n = 14..23`,
`r7encode matrix`): identical output, no failed check.

* **NMH's `tour-encode.c`** (`refs/directed-ramsey-src/…/encoding/tour-encode.c`,
  `limit = 5040 = 7!`): the 3-cycle branch and the auxiliary 3-cycle clauses are never reached
  (a 7-set has at most `7!` orderings), so the variables `C(n,2)+1 … C(n,2)+C(n,3)` counted in the
  header `5456` of the `23X` and `ST26` instances never occur; the `ST25` headers say `C(n,2)`
  (`496`, `528`), as in NMH's logs. Observations: (i) the "reduced clause" heuristic of
  `printClause` only checks that the opposite corner `mask ^ xor` of the cube is a listed
  ordering, not the whole subcube; it is nevertheless sound here, because the single-bit
  neighbours of a linear order are adjacent transpositions and the corner is a linear order only
  if those transpositions are disjoint (then every sub-flip is a linear order). The Lean
  version does not rely on this: every clause passed the local check. (ii) The `while (iter)`
  loop never prints in its second pass. (iii) `permutations` allocates a clause buffer per
  accepted permutation and never frees it (642 MB RSS for `23A-p-Y8`; the Lean version needs
  27 MB). (iv) `while ((x % 2) == 0)` would not terminate for `x = 0`; it cannot happen because
  the listed masks are distinct. (v) The `p cnf … 5000` placeholder header is replaced by
  `scripts/stage4_instances.py`, as documented there. None of this changes the CNFs.
* **`src/encode.c`** in "3-cycle mode" (`limit = 1`): a 7-set with exactly one ordering
  compatible with the fixed arcs gets a direct clause, not a 3-cycle clause (2,608,200 of the
  9,007,047 clauses of `24A-p-O21s`), as the C program's comment says for `≤ limit` orderings;
  "3-cycle mode" in `data/stage3_manifest.json` means this. `cyc_lit` keeps creating 3-cycle
  variables after a constant-true literal has satisfied the 3-cycle clause; this never happens,
  since 7-sets with a fixed 3-cycle are pruned. No discrepancy with the documentation was found.

## Remaining `sorry`s

None.

## Next milestones

1. **Cube trees in Lean.** A compiled checker that reads a results directory (`cubes.icnf`, the
   per-cube records) and builds the `Closed` derivation of `R7lean/CubeCover.lean`, reducing
   each F7-CNF axiom to per-leaf axioms `¬ Satisfiable (withCube F c)` (what each checked LRAT
   proof establishes). The level-0 cover condition is all `2^10` sign patterns on 10 variables
   and could be proved outright in the kernel. Small LRAT proofs could be replayed with Lean's
   verified LRAT checker (`Std.Tactic.BVDecide.LRAT`); the leaf proofs (thousands of
   solver-hours) stay external.
2. **F2–F6 ↔ enumeration.** Formalize the pivot decomposition (Proposition `prop:pivotdec`)
   and completeness (Proposition `prop:complete`), so that the catalogue axioms reduce to
   "each job formula plus its blocking clauses is UNSAT" (job CNFs produced by a Lean encoder,
   with the same certified-check design and sha256 comparison as here) and "each recorded
   model is isomorphic to a listed class" (explicit isomorphisms checked by `decide`, as in
   `NMHIso.lean`, instead of trusting `labelg`). `R5_le_14` stays computational; it could be
   certified by the same pivot enumeration from the TT₄-free lists (`data/tt4free/`).
3. **Data.** Kernel-checked sanity facts by `decide` (e.g. `Y8` has 15 three-cycles, `O21s` is
   regular), as a guard against a misread file.
