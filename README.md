# R(7) ≤ 46 for tournaments

Every tournament on 46 vertices contains a transitive subtournament on 7 vertices. Hence the
directed Ramsey number satisfies 34 ≤ R(7) ≤ 46 (previous upper bound 47, Neiman, Mackey and
Heule 2022).

This repository contains the proof's code, inputs, result records and paper:

- `paper/r7le46.tex`: the paper (build with `tectonic paper/r7le46.tex`).
- `notes/RUN2.md`: how the final computation (run 2, 5–8 November 2026) was carried out and checked.

## How the result is checked

- **SAT computations.** The proof uses three computations: complete lists of the TT6-free
  tournaments on 21–26 vertices; five new SAT instances on 46 vertices; and the 28 SAT
  computations of Neiman, Mackey and Heule, re-run here. Each is solved by CaDiCaL with an LRAT
  proof. Every proof was checked by two checkers: a patched `lrat-check` from drat-trim, and the
  formally verified `cake_lpr` (CakeML). Cube-and-conquer covers are checked as well.
- **Coverage.** That makes 189,018 enumeration jobs, 47,495 leaves for the five new instances and
  32,692 leaves for NMH's instances. Every one was accepted by both checkers.
- **Lean.** A Lean 4 project (`r7lean/`) derives the theorem from twelve axioms: R(5) ≤ 14 and
  eleven statements of the computational results.
- **Not checked.** Section 7 of the paper lists what the checkers do not cover.

## Layout

| Path | Contents |
|---|---|
| `src/` | enumerator (`pivenum.cpp`), encoders (`encode.c`, `ttenc.h`), soundness checkers (`cnf_sound.c`, `tri_sound.c`), tournament utilities |
| `scripts/` | enumeration and certification, cube-and-conquer (`make_cubes.py`, `run_cubes.py`, `stream_solve.py`, `cnc_summary.py`), cloud drivers (`scripts/cloud/`) |
| `scripts/audit/` | independent checks: `closure.py` (cube trees), `modelfix.py` (enumeration models), `union_audit.py` (both checkers on every leaf), `jsonl_check.py`, `cake_sample.py` and `dualcheck.sh` (second checker) |
| `data/` | input tournaments and SHA-256 manifests of all 33 SAT instances |
| `results/` | run 2 records and summaries: `enum/`, `stage3/`, `stage4/`, `cake/`; run 1 archived in `results/run1/` |
| `r7lean/` | Lean 4 formalisation |
| `tools/` | patched `lrat-check` (drat-trim, MIT) and `cake_lpr` (its own licence) |
| `tests/` | tests of the checkers, encoders and tools |

The per-proof logs of both checkers (271,883 JSON files) are too large for git. They are in
`run2-cakelogs.tar.gz` in the Zenodo record
([doi:10.5281/zenodo.24050255](https://doi.org/10.5281/zenodo.24050255)); its SHA-256 is given in
`notes/RUN2.md`. Unpack it at the
repository root before running `scripts/audit/union_audit.py`. Third-party inputs (Neiman–Mackey–Heule's
repository and the catalogue files of Lohn, Lambert and Heule) are fetched by
`scripts/fetch_refs.sh`, not redistributed.

## Checking the records without re-running the solvers

```sh
python3 -I scripts/audit/closure.py results/stage3/24A-p-O21s      # each cube tree closes
python3 -I scripts/stage12_check.py                                  # catalogue facts
python3 -I scripts/audit/union_audit.py results/stage3 results/cake/stage3-recheck   # needs the log archive
cd r7lean && lake build                                              # the Lean reduction
```

Re-checking the proofs themselves means re-running the solver: about 5,400 solver-hours. The
cloud drivers in `scripts/cloud/` do this on AWS.

## Licences

- Code: MIT (`LICENSE`).
- Data, result records, notes and the paper text: CC BY 4.0.
- Third-party files in `tools/` keep their own licences.

## Use of AI tools

This work was carried out with an AI assistant, Claude (Anthropic), working under the author's
direction. Every commit names it as co-author. See Section 9 of the paper.

## Citation

Ahmet Tahir Mat, *The directed Ramsey number R(7) is at most 46*, 2026. Archived snapshot:
[doi:10.5281/zenodo.24050255](https://doi.org/10.5281/zenodo.24050255).
