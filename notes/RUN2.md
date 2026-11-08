# Run 2 (5–8 November 2026)

Run 2 repeats every computation of run 1 with the patched `lrat-check` (FEASIBILITY §14) and adds a
second, formally verified checker, `cake_lpr`, to every proof. The checker gap fixed for run 2 was
already known upstream (drat-trim issue #42, PR #43); we did not discover it.

Run 1 is archived in `results/run1/`. Everything below is run 2. All times are UTC.

## Checking

- Every proof was streamed to both checkers by `scripts/audit/dualcheck.sh` (via `TR_LRAT_CHECK`).
- `DUALCHECK_REQUIRE=lrat`: the run's verdict is the patched `lrat-check`'s, under the strict rule
  (exit 0, `c VERIFIED`, no `FAILED`). `cake_lpr`'s verdict is logged per proof in a JSON file
  (`results/<stage>/cakelog/`, field `both_verified`), so a `cake_lpr` failure never stopped a run.
- `cake_lpr` heap: enumeration 1024 MiB, Stage 4 2048 MiB, Stage 3 14336 MiB
  (`DUALCHECK_CAKE_HEAP`). Its heap must hold the parsed formula (about 12.9 bytes per DIMACS byte,
  `tools/cake_lpr/README.md`); Stage 3 formulas are 1.07 GB.
- Proofs that were checked by `lrat-check` only were re-solved afterwards and checked by both, with
  `scripts/audit/cake_sample.py` (`enum --ids`, `cubes --ids`).

## Stages 1–2: enumeration, n = 21…26

- One m8g.24xlarge (eu-north-1c, launched 11-05 11:13), `run_stage12c.sh`: n = 26, 25, 24, 23, 22, 21.
- It switched to dual checking at 12:56 on 11-05 (commit f7fcb73). Jobs before that were checked by
  `lrat-check` only: all of n = 26…23 and the first 10,578 jobs of n = 22.
- Done 11-06 03:30, rc 0. `scripts/stage12_check.py`: GO 1, GO 2, "ST26 unique: CERTIFIED".
  `scripts/audit/modelfix.py`: 204,350 models, 0 that do not fit their job.
- Dual coverage:
  - during the run: n = 21, 167,798 / 167,798 jobs both VERIFIED; n = 22, 7,095 jobs both VERIFIED;
  - re-checked by both with `cake_sample.py enum` (`results/cake/enum/`): n = 22, the 10,578 listed
    jobs (`data/run2_n22_lrat_only.json`); n = 23, 3,086; n = 24, 414; n = 25, 46; n = 26, 1.
    Every summary says `"ALL VERIFIED BY BOTH": true`.
  - No job had an `lrat-check` / `cake_lpr` disagreement.

## Stage 4: NMH's 28 instances

- Same machine, started by itself at 03:31 on 11-06 (`run_stage4.sh stage4 96 60`): all 28 instances
  side by side, 3 workers each, time limits 1800, 3600, 1800, 7200, ∞ s for levels 0–4.
- Done 11-07 00:47, rc 0: all 28 `ALL CLOSED`, no SAT cube, no failed check; 1,265.7 solver-hours.
- `scripts/audit/closure.py`: 28/28 OK. `scripts/audit/jsonl_check.py`: no flagged record.
- 32,692 UNSAT leaves. 32,684 were checked by both during the run. For 8 deep leaves (all at level 4,
  solve times 10.5k–15.9k s, proofs 4.3–7.0 GB) `cake_lpr` stopped with "CakeML heap space exhausted"
  at 2048 MiB; `lrat-check` had verified them. `cake_lpr` verified every Stage 4 proof up to 3.6 GB at
  that heap. The 8 leaves (`data/run2_stage4_cake_heap_retry.json`) were re-solved and checked by both
  with a 16384 MiB heap: all 8 VERIFIED by both (`results/cake/stage4-heapretry/`).
- `scripts/audit/union_audit.py results/stage4 results/cake/stage4-heapretry`:
  "EVERY LEAF CHECKED BY BOTH lrat-check AND cake_lpr", 0 disagreements.

## Stage 3: the five new instances

- Time limits 600, 1800, ∞ s for levels 0–2 (as in run 1). No level-1 cube timed out.
- Machines (spot, eu-north-1): a first m8g.24xlarge ran 11-05 11:13–13:10 with `lrat-check` only;
  then r8g.24xlarge (742 GiB) with dual checking from 13:10 on 11-05. The memory of `cake_lpr`
  (about 14 GiB per worker) limited a 24xlarge to 35 workers.
- 15 spot interruptions for lack of capacity (11-05 17:16 to 11-08 00:12). After each one the
  affected instances were resumed on a new machine from the records synchronised to the Mac
  (r8g.24xlarge, r8g.16xlarge, r8g.12xlarge, r8g.8xlarge, r7g.12xlarge, r7g.8xlarge; eu-north-1a/b/c).
  From 11-07 01:00 the instances were spread over several smaller machines. Work in progress at an interruption left no
  record and was redone. Machine list: `results/aws_ledger.csv`.
- All five `ALL CLOSED`: 24A 11-08 01:39, 24C 03:22, 24D and 24E 03:23, 24B 03:36. No SAT cube, no
  failed check. `closure.py` 5/5 OK; `jsonl_check.py`: only three level-0 UNKNOWN records shorter than
  the time limit (24A cube 58, 24B cube 13, 24C cube 83) from the first, lrat-only machine; each was
  split into its 16 children like any timed-out cube, which the cover lemma (paper, `lem:cover`) allows.
- Leaves: 24A 9,484; 24B 9,709; 24C 9,169; 24D 9,604; 24E 9,529; total 47,495.
- 47,236 leaves were checked by both during the run. The other 259 (24A 52, 24B 49, 24C 57, 24D 53,
  24E 48: level-0 leaves from the first, lrat-only machine) were re-solved and checked by both with
  `cake_sample.py cubes --ids` (`results/cake/stage3-recheck/`), all `"ALL VERIFIED BY BOTH": true`.
- `scripts/audit/union_audit.py results/stage3 results/cake/stage3-recheck`:
  "EVERY LEAF CHECKED BY BOTH lrat-check AND cake_lpr", 0 disagreements.

## Cost

AWS spot, metered from public spot prices (`results/aws_cost.json`, `scripts/cloud/cost_meter.py`):
run 1 US$39.22, run 2 US$88.08, total US$127.30. EBS volumes and data transfer are not included.

## Per-proof checker logs

The per-proof JSON logs of both checkers (`results/stage3/cakelog/`, `results/stage4/cakelog/`,
`results/enum/cakelog/` and the `dualcheck/` directories of the re-checks in `results/cake/`;
271,883 files, about 1.1 GB) are not in git. They are archived as `results/run2-cakelogs.tar.gz` (Zenodo, doi:10.5281/zenodo.24050255)
(51,525,521 bytes, SHA-256
`98d937fea0f76d1271ec529ae8a4a0cfdcccdbfb1aab2daf8f08b6a35557881d`), deposited with the
archived snapshot. `scripts/audit/union_audit.py` needs them unpacked in place.
