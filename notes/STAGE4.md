# Stage 4: NMH's computations re-run with checked LRAT proofs

Date: 4 Nov 2026. Built and validated on the Mac. Nothing has been launched on AWS for Stage 4.

NMH is Neiman, Mackey and Heule, "Tighter bounds on directed Ramsey number R(7)", [arXiv:2011.00683](https://arxiv.org/abs/2011.00683) v2. Their repository [neimandavid/Directed-Ramsey](https://github.com/neimandavid/Directed-Ramsey) has the inputs, the encoder and the solver logs. It has no DRAT or LRAT proofs. Stage 4 re-runs every one of their long SAT computations as cube-and-conquer with streamed, checked LRAT proofs. After Stage 4, our R(7) ≤ 46 result rests on no unchecked computation, apart from the TT5-free base catalogue (which Stage 0 re-derived and cross-checked).

## 1. Verdict: go

**Go.** All 28 CNFs are built and pass the equivalence checks in §3. The driver is tested end to end, including the SAT, resume and failure paths. The cost measured on the Mac is small against the budget:

- **Central:** about 1,100 Graviton4 vCPU-hours, or 13.5 h on one c8g.24xlarge spot box, about US$6.
- **Tail:** about 2,200–2,650 vCPU-hours, or 27–32 h on one box, US$12–16.

Both fit the US$100–120 set aside for Stage 4, by a factor of about 8. The plan is one c8g.24xlarge box for all 28 instances, started once stage12 has terminated, next to the Stage 3 box. It should finish before the Stage 3 box frees the second quota slot (about 5 Nov, 20:00 UTC). A second box is not needed, but a balanced split is given in §6.

## 2. The instances: 28, not 27

The 27 runs in NMH's Fig. 6 ("the 27 hard instances") are:

- the 25 instances `23X -p- Y8`, X = A, …, Y (their §5.2.3, logs in `log23/`);
- `ST25 -p- H6` and `ST25 -p- W7` (§5.2.2, logs in `log25/`).

Their §5.2.1 uses a 28th computation, `ST26 -p- TT5` ("Using CaDiCaL, we found that ST26 connected through a pivot vertex to TT5 is unsatisfiable"). They published no input, log or run time for it. Our argument for n = 46 needs it too (FEASIBILITY §3.1, item 1), so Stage 4 runs all 28. Earlier notes called this set "27"; that count was off by one.

| Instance | n | Free arcs | Header vars | Clauses | Bytes | = NMH log | NMH run (log) | CNF sha256 |
|---|---|---|---|---|---|---|---|---|
| `ST26-p-TT5` | 32 | 130 | 5456 | 1,099,282 | 48,089,224 | no log | none published | `fa91193c05eda98fc16b1019cdb12edce3c5d3395df327043fc0963c976dfb3b` |
| `ST25-p-H6` | 32 | 150 | 496 | 1,687,063 | 74,752,227 | yes | CaDiCaL 1.5.2, 23.9 h, 88M conflicts | `2a4376a8419e20910caea75915e346fc55a1bbd02e7361b958d5dc62512f0093` |
| `ST25-p-W7` | 33 | 175 | 528 | 2,603,275 | 115,895,955 | yes | CaDiCaL 1.5.2, 33.5 h, 96M conflicts | `5b92889659ecd4cb55056a824b26d8e88aa803cc9dfbddb992ebc730f1036661` |
| `23A-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,147,858 | yes | CaDiCaL 1.3.1, 121.0 h, 354M conflicts | `fe1fb6a821aaa2871c1809f2425e19b4299ccc988a5defa2b0e86f055054636f` |
| `23B-p-Y8` | 32 | 184 | 5456 | 2,364,374 | 105,621,643 | yes | CaDiCaL 1.3.1, 79.4 h, 265M conflicts | `d71ad22bfe702570c99be74bf8a107932a44a6f8cfcbf0ea3e114f4b77b19481` |
| `23C-p-Y8` | 32 | 184 | 5456 | 2,364,374 | 105,622,284 | yes | CaDiCaL 1.3.1, 97.5 h, 308M conflicts | `91bf97ee7d97534f01e9908a8d333ffb8fd6d687b4b9eae09b3cf709511f9312` |
| `23D-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,146,650 | yes | CaDiCaL 1.3.1, 157.1 h, 427M conflicts | `e9b59ad3b771d4218fc7d8430aea5305e223ef05e53a409cc545f51a2fd1bd25` |
| `23E-p-Y8` | 32 | 184 | 5456 | 2,343,727 | 104,733,141 | yes | CaDiCaL 1.3.1, 203.9 h, 543M conflicts | `ca24815c2f30afe0e16c7c78f6eb8bd28454f174ac8e84f6607dd46bce3618fb` |
| `23F-p-Y8` | 32 | 184 | 5456 | 2,343,727 | 104,737,188 | yes | CaDiCaL 1.3.1, 230.9 h, 609M conflicts | `b184585c0b4d6c61cc27dde7c882cf4560d6b707ae98bd49cc6abfc9f592b32e` |
| `23G-p-Y8` | 32 | 184 | 5456 | 2,343,727 | 104,733,915 | yes | CaDiCaL 1.3.1, 212.2 h, 560M conflicts | `6d24856dac70ae137a644edaf938e3f4a28f80fd07b0f08defa767f78e7706a8` |
| `23H-p-Y8` | 32 | 184 | 5456 | 2,343,727 | 104,737,269 | yes | CaDiCaL 1.3.1, 249.9 h, 650M conflicts | `a5030a5e4577b999f3d17c6dae7d4ab3ff3d4c6915405b67e0804e2f3103ffb4` |
| `23I-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,144,196 | yes | CaDiCaL 1.3.1, 203.7 h, 495M conflicts | `212d48ec13cbdcdfedb86e128a4cac58535dbaf7969c5ce379332253ce0059b1` |
| `23J-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,143,575 | yes | CaDiCaL 1.3.1, 240.0 h, 589M conflicts | `c0061227cc82079fc32965d5755fc3b30cc620e4251df681577865647bdfb3f9` |
| `23K-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,145,616 | yes | CaDiCaL 1.3.1, 138.5 h, 383M conflicts | `757bac7849e73b1a99b40d37425f92f9f93d6d044576a0c587b106c754649f30` |
| `23L-p-Y8` | 32 | 184 | 5456 | 2,343,727 | 104,735,292 | yes | CaDiCaL 1.3.1, 242.6 h, 618M conflicts | `df0001f097bf5c66426fa01552310461dbef88ce0e8e50bdd9cc186f2283cb5c` |
| `23M-p-Y8` | 32 | 184 | 5456 | 2,364,374 | 105,617,376 | yes | CaDiCaL 1.3.1, 94.3 h, 300M conflicts | `62fb39b340083582258c6c0b024a449b95f7f688a238037ec259d979d31eb17c` |
| `23N-p-Y8` | 32 | 184 | 5456 | 2,364,374 | 105,616,829 | yes | CaDiCaL 1.2.1, 235.5 h, 390M conflicts | `dd73b2ce49bdf2274dcacc71e5f66bad5f7d6cd1994fe9707363040efeea3d94` |
| `23O-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,141,305 | yes | CaDiCaL 1.2.1, 310.1 h, 460M conflicts | `2fdc7dd0d397ce6006c90260c236944c60df668e37f336b35d7fb8e4004d694a` |
| `23P-p-Y8` | 32 | 184 | 5456 | 2,364,374 | 105,622,322 | yes | CaDiCaL 1.2.1, 198.8 h, 342M conflicts | `38090a44dd5846b9348a693e99187281e2459603259e6b7bd80e54004a7c1e60` |
| `23Q-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,147,085 | yes | CaDiCaL 1.2.1, 247.8 h, 394M conflicts | `de027f4cfadbb085b1b774280eee58cecae6a94ed25e516aca84e589ff7d32c6` |
| `23R-p-Y8` | 32 | 184 | 5456 | 2,364,374 | 105,617,578 | yes | CaDiCaL 1.2.1, 158.6 h, 293M conflicts | `a41d6a51c6ebd74729aa0f73c781c84bcfd3474e00cbf10636b5175761bef82e` |
| `23S-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,146,971 | yes | CaDiCaL 1.2.1, 431.6 h, 643M conflicts | `ac2c79ff852f1b9ad2e1567498d8584a995eac783285a116d4b32b1e189253c3` |
| `23T-p-Y8` | 32 | 184 | 5456 | 2,364,374 | 105,618,756 | yes | CaDiCaL 1.2.1, 164.9 h, 312M conflicts | `8e33d799df9da5ba809ae36e21f78a6bf3dea3a942bd4535014406971d660839` |
| `23U-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,143,964 | yes | CaDiCaL 1.2.1, 242.6 h, 401M conflicts | `fa08aafbcd6f7fb399831f4d04133e9924d3ff5b94df9e0c3a559b574e16d2c8` |
| `23V-p-Y8` | 32 | 184 | 5456 | 2,353,250 | 105,149,401 | yes | CaDiCaL 1.2.1, 327.4 h, 483M conflicts | `725b6bb2a37b125af28853b4ad93c54036cc46fb7679f108adc893b28aa678bc` |
| `23W-p-Y8` | 32 | 184 | 5456 | 2,196,265 | 98,527,941 | yes | CaDiCaL 1.2.1, 68.1 h, 139M conflicts | `6b2e6de60f0e8ca1a03f46186d10d5015b0d93dd4929b94ac8356d5293ee8af6` |
| `23X-p-Y8` | 32 | 184 | 5456 | 2,196,265 | 98,529,993 | yes | CaDiCaL 1.2.1, 72.2 h, 144M conflicts | `033d957315cc4fe8e9d6f1f5670b4e9ecc31e57b38717a44ca1c552a1d0c47a5` |
| `23Y-p-Y8` | 32 | 184 | 5456 | 2,219,145 | 99,413,410 | yes | CaDiCaL 1.2.1, 14.5 h, 48M conflicts | `bb8a6acf81964d3fa5f68c326b65e9c28651cd4569a86180433b114b47bbffff` |

"= NMH log" means that our CNF has the header, the clause count and the byte count that NMH's CaDiCaL log reports for the file it read. The full records, including the sha256 of every input and of the encoder source, are in `data/stage4_manifest.json`.

## 3. Equivalence: our CNF says exactly what NMH's run said

**Choice: NMH's own encoder on NMH's own inputs.** This is the strongest form of "we re-checked every computation NMH ran": the formula we solve is, as far as anything published lets anyone check, the formula their solver read. Using our encoder (`build/encode`) would re-check the same mathematical statement, but it would be a different formula. The checks below make the NMH formula safe to rely on, so nothing is gained by switching.

How each CNF is made (`scripts/stage4_instances.py`):

1. **Encoder.** NMH's `encoding/tour-encode.c`, compiled as in their Makefile (`gcc tour-encode.c -O2`).
2. **Inputs.** NMH's own matrices `log23/23X-p-Y8.txt` and `log25/ST25-p-{H6,W7}.txt`. For `ST26-p-TT5` we use our own matrix `data/ST26-p-TT5.txt`: ST27 (`data/ST27.txt`) minus vertex 0, which is ST26 (unique, vertex-transitive), then the pivot, then TT5.
3. **Command.** `tour-encode N 7 INPUT 5040`. The limit 5040 = 7! means that every 7-set gets direct clauses, so there are no 3-cycle variables.
4. **Header.** The encoder writes the placeholder header `p cnf 5456 5000`. We replace the clause count with the real one. The variable count stays 5456 (= C(32,2) + C(32,3)) as in all 25 `log23` headers, except for the two ST25 instances, whose log headers say C(n,2) (496 and 528).

**Results:**

- **All 27 CNFs that have a log reproduce NMH's header, clause count and byte count exactly.** Example: `23A-p-Y8` has `p cnf 5456 2353250` and 105,147,858 bytes, as in the log.
- This also settles the encoding NMH used. The Y8 instances are direct encodings with 184 free arc variables, all other arcs fixed by unit clauses. The 5456 in the header is only the encoder's placeholder count. FEASIBILITY §2.4 said these instances "use triangle variables"; they do not. The default limit 1 gives 470,800 clauses for `23A-p-Y8`, and the limits 2, 4 and 8 also fail to match; only 5040 matches.
- **A caveat.** NMH's CNF files themselves are not published, so byte identity cannot be checked directly. What we check is the same encoder source, the same input, a deterministic encoder, and an identical size and clause count. The argument below does not depend on this point.

**Input structure** (`structure()` in the script; all 28 pass):

- Each input is a pivot instance X → p → Z. The arcs inside X and inside Z are fixed, X → p → Z holds, and exactly the X×Z pairs are free.
- X is isomorphic to our own class of the same letter, checked by nauty canonical form against `data/I23_X.txt`. Those classes come from our own ST27 construction and from McKay's doubly regular tournaments (`scripts/make_data.py`).
- X is TT6-free, and the 25 X classes are pairwise non-isomorphic.
- Z is isomorphic to our Y8, H6, W7 or TT5 (`data/`).

**Soundness of every clause** (`src/cnf_sound.c`, new, independent of both encoders). The claim checked is that every clause holds in every TT7-free completion of the input. Then "the CNF is UNSAT" implies "the input has no TT7-free completion". Completeness of the encoding is not needed for that direction, so it is not checked. A clause passes in one of three ways:

- it contains a literal that is true on a fixed arc (this covers the unit clauses, which must agree with the input);
- it is a tautology;
- there is a 7-set S, containing every vertex of the clause, such that every orientation of S's free pairs that falsifies the clause makes S transitive.

**All 28 CNFs are SOUND, with 0 failures.** For example, `23A-p-Y8` has 312 units on fixed arcs and 2,352,938 clauses with a witness 7-set. The check takes about 1 s per instance.

**Tests:**

- `tests/test_cnf_sound.py`, on 40 random partial tournaments (n = 6–10, k = 4–5):
  - the models of NMH's CNF are exactly the TT_k-free completions, by brute force in both directions, so NMH's encoder is right on these cases;
  - cnf_sound accepts NMH's CNFs and ours;
  - of 240 mutated clauses, cnf_sound accepts no unsound one, and 42 are unsound by brute force;
  - a wrong header is reported.
- `tests/test_stage4_driver.py` runs the driver end to end (section 4).

**Together:**

1. LRAT-checked UNSAT of the CNF, cube by cube, plus a checked cover of the cubes;
2. every clause sound for the input;
3. the input equals the configuration the R(7) ≤ 46 argument needs, up to isomorphism of X and of Z.

These give "no TT7-free completion" without trusting either encoder or CaDiCaL. What must be trusted is lrat-check, cnf_sound, the cover and split checks in `cnc_summary.py`, and the nauty isomorphism check. Matching NMH's logs shows that this is the computation they ran.

On the server, `run_stage4.sh` rebuilds each CNF from the fetched NMH repository and refuses any instance whose input, encoder source or CNF differs from the sha256 values recorded here.

## 4. Driver: `scripts/cloud/run_stage4.sh`

```
nohup bash scripts/cloud/run_stage4.sh STAGE WORKERS [GRACE_MIN] > results/STAGE.log 2>&1 < /dev/null &
STAGE = stage4 (all 28) | stage4-<codes>: A..Y = 23X-p-Y8, t = ST26-p-TT5, h = ST25-p-H6, w = ST25-p-W7
env (optional): SLOTS=all instances  TIMEOUTS=1800,3600,1800,7200,0  MINFREE=8  POLL=20
```

*(Defaults changed on 5 Nov 2026 for run 2 to the schedule that finished run 1: all instances side by side, five levels. Run 1 started with SLOTS=6 and TIMEOUTS=1800,3600,0, the values described below.)*

The steps are:

1. Fetch NMH's repository if `refs/directed-ramsey-src` is missing. This is a plain `curl` of the codeload tarball, with the same generic User-Agent as `fetch_refs.sh`.
2. For every instance, in parallel:
   - `stage4_instances.py build`: NMH's encoder, then the input, encoder and CNF sha256 must equal the manifest;
   - `make_cubes.py --k 10 --maxvar C(n,2)`, a static split into 1024 cubes on the 10 most frequent arc variables.
3. Conquer, longest expected first, SLOTS instances side by side with WORKERS/SLOTS workers each. A queue starts the next instance when one finishes. Each instance runs `run_cubes.py --timeouts 1800,3600,0 --split 4 --nice 5 --min-free-gb 8`, exactly as in Stage 3: CaDiCaL `--lrat` streams into lrat-check, and an unfinished cube is split into 16 children at the next level.
4. **A SAT cube.** run_cubes saves the model. The driver checks it with `verify_model.py --numbering nmh --model`, which checks that every CNF clause is satisfied, that the model agrees with the fixed arcs, and that the completion is TT7-free. The driver then writes `results/STAGE.SAT`, logs `!!!!!!!! SAT …`, kills every solver of the stage and does not start new instances. A rerun refuses to start while `results/STAGE.SAT` exists.
5. **A failed LRAT check** stops that instance and is logged. A rerun retries the cube.
6. **The end.** `cnc_summary.py` runs per instance. It checks the cover by LRAT, the split structure and that every leaf is VERIFIED, and it must print ALL CLOSED. The driver then writes `results/STAGE.DONE` (0 only if every instance is ALL CLOSED) and moves the power-off to GRACE minutes, never past the user-data hard stop, exactly as `run_stage.sh` does. `run_stage.sh` itself is unchanged.
7. **Resume.** Rerunning the same command skips CNFs whose sha256 is already right, existing cubes, finished cubes (`results.jsonl`) and instances whose summary is ALL CLOSED. After a spot reclaim: launch a new box, run `push.sh IP --results-sub stage4`, and run the same command (§6).

`watch.sh` and `push.sh`'s guard both match `^bash scripts/cloud/run_stage`, which also covers `run_stage4.sh`, and `sync_back.sh` copies all of `results/`. All three work unchanged. Progress against the projection: `python3 scripts/stage4_progress.py` (Mac, on the synced results).

The tests, `tests/test_stage4_driver.py`, use small TT5 instances in a temporary copy of the repo, and all pass:

- an UNSAT instance ends ALL CLOSED with DONE = 0;
- a rerun adds no cube records;
- a queue of two instances through one slot works;
- a failed LRAT check is logged and the stage ends NOT CLOSED with DONE = 1;
- a SAT instance has its model verified, `.SAT` is written, the stage stops with DONE = 1, and a rerun refuses to start;
- a wrong CNF sha256 is refused;
- a corrupted model is rejected.

## 5. Cost projection (measured on this Mac)

**How it was measured** (`scripts/stage4_sample.py`, raw records in `notes/stage4/mac_samples.jsonl`):

- 136 random level-0 cubes from 12 of the 28 instances. The cubes come from the driver's own split (K = 10, 1024 cubes per instance).
- Each cube was solved exactly as on the server: `stream_solve.py`, CaDiCaL 3.0.1 `--lrat` streamed into lrat-check, all VERIFIED, with a 600 s limit (none reached it).
- 4 workers at `nice 10`.
- The instances were chosen to cover the range:
  - the hardest by NMH hours (23S) and by conflicts (23H, 23L);
  - 23O (second by hours);
  - the middle (23Q, 23K, 23B);
  - the easy ones (23W, 23Y);
  - all three ST instances.
- **The cost of a cube is CPU time, cadical plus lrat-check** (`/usr/bin/time -l`), not wall time. The Mac was shared with other heavy jobs during the run: load median 8.4 on 10 cores, peak 50. CPU time is much less sensitive to that, but niced jobs may have landed on efficiency cores, so these numbers are, if anything, high. The first 34 pilot cubes have wall time only.
- lrat-check is 7.5% of the CPU, mostly re-reading the CNF for each cube (1.5–13 s per cube).
- Sampling used 1.86 Mac core-hours. Everything done on the Mac for Stage 4 used about 2.3 core-hours.

**Estimator** (`scripts/stage4_project.py`):

- A sampled ST instance is 1024 × its mean cube cost.
- Each 23X-p-Y8 is a ratio estimate: the sampled Y8 instances' total (1024 × mean each) divided by their NMH conflicts, times that instance's NMH conflicts. This gives 0.042 Mac core-hours per million NMH conflicts.
- NMH's conflicts are a weak predictor of the cube-and-conquer cost of a single instance. 23B samples about 2× above its ratio estimate and 23Q 1.3× above it, while 23S samples 0.7× of it. The ratio is therefore used for the total, not for single instances. A cross-check, with sampled instances at their own mean and the rest at the plain mean of the sampled Y8 instances, gives 434 Mac core-hours, against 441.

| Instance | Cubes sampled | Mean / median / max s per cube | 1024 x mean (Mac core-h) | NMH conflicts | Projection (Mac core-h) | vCPU-h |
|---|---|---|---|---|---|---|
| `23H-p-Y8` | 17 | 86 / 57 / 414 | 24.5 | 650M | 27.0 | 67 |
| `23S-p-Y8` | 24 | 65 / 56 / 220 | 18.4 | 643M | 26.7 | 67 |
| `23L-p-Y8` | 8 | 61 / 41 / 150 | 17.3 | 618M | 25.6 | 64 |
| `23F-p-Y8` | - | - | - | 609M | 25.3 | 63 |
| `23J-p-Y8` | - | - | - | 589M | 24.5 | 61 |
| `23G-p-Y8` | - | - | - | 560M | 23.3 | 58 |
| `23E-p-Y8` | - | - | - | 543M | 22.6 | 56 |
| `23I-p-Y8` | - | - | - | 495M | 20.6 | 51 |
| `23V-p-Y8` | - | - | - | 483M | 20.1 | 50 |
| `23O-p-Y8` | 8 | 58 / 36 / 125 | 16.4 | 460M | 19.1 | 48 |
| `23D-p-Y8` | - | - | - | 427M | 17.7 | 44 |
| `23U-p-Y8` | - | - | - | 401M | 16.7 | 42 |
| `23Q-p-Y8` | 12 | 74 / 70 / 158 | 20.9 | 394M | 16.4 | 41 |
| `23N-p-Y8` | - | - | - | 390M | 16.2 | 41 |
| `23K-p-Y8` | 6 | 63 / 30 / 243 | 17.9 | 383M | 15.9 | 40 |
| `23A-p-Y8` | - | - | - | 354M | 14.7 | 37 |
| `23P-p-Y8` | - | - | - | 342M | 14.2 | 36 |
| `23T-p-Y8` | - | - | - | 312M | 12.9 | 32 |
| `23C-p-Y8` | - | - | - | 308M | 12.8 | 32 |
| `23M-p-Y8` | - | - | - | 300M | 12.5 | 31 |
| `23R-p-Y8` | - | - | - | 293M | 12.2 | 30 |
| `23B-p-Y8` | 6 | 79 / 62 / 217 | 22.6 | 265M | 11.0 | 28 |
| `ST25-p-H6` | 6 | 33 / 25 / 93 | 9.4 | 88M | 9.4 | 24 |
| `ST25-p-W7` | 12 | 23 / 13 / 104 | 6.6 | 96M | 6.6 | 17 |
| `23X-p-Y8` | - | - | - | 144M | 6.0 | 15 |
| `23W-p-Y8` | 6 | 27 / 28 / 44 | 7.8 | 139M | 5.8 | 14 |
| `ST26-p-TT5` | 15 | 11 / 9 / 28 | 3.0 | no log | 3.0 | 8 |
| `23Y-p-Y8` | 16 | 13 / 11 / 32 | 3.6 | 48M | 2.0 | 5 |

**Totals.** 441 Mac core-hours; a bootstrap over the sampled cubes gives a 90% interval of 363–527. The conversion to Graviton4 is × 2.5:

- The 11-03 calibration: one fully loaded Graviton4 vCPU runs our jobs at about 0.4× an unloaded Mac core.
- A direct check on cadical with big CNFs: Stage 3's cubes 463 and 886 of 24A took 227 s and 221 s on the server, against 94 s on the Mac.

Box hours assume 85% use of the 96 vCPUs (90 workers, queue tails). Prices: c8g.24xlarge spot about US$0.445/h, up to 0.50.

| Case | vCPU-h | One 96-vCPU box | Two boxes | US$ |
|---|---|---|---|---|
| Central | 1,100 | 13.5 h | 6.7 h | 6.0–6.7 |
| Bootstrap 95th percentile | 1,320 | 16.1 h | 8.1 h | 7.2–8.1 |
| Tail: 2× central (heavy-tailed cubes the sample missed, estimator error) | 2,200 | 27 h | 13.5 h | 12.0–13.5 |
| Tail with a Graviton factor of 3 | 2,640 | 32 h | 16 h | 14.4–16.2 |

For comparison, NMH's single runs took about 4,800 m5d CPU-hours without proofs. Cube-and-conquer with checked proofs needs about a quarter of that in Graviton vCPU-hours.

**Cube depth and time limits:**

- K = 10 gives 1024 cubes per instance. The mean cube costs 10–90 Mac-s (about 25–220 s on Graviton). The largest sampled cube was 414 Mac-s, about 1,035 s on Graviton.
- Deeper splits would mostly add per-cube overhead (CNF parsing by both programs, 2–5 Mac-s). Shallower ones would make the tail cubes long.
- `TIMEOUTS=1800,3600,0` (Graviton seconds): no sampled cube would reach the first limit. The rare longer cubes are split into 16 children, at a cost of at most 30 min each.

**Memory** (Mac peak per cube):

- CaDiCaL up to 1.50 GB (typically 0.5–1.3 GB);
- lrat-check up to 0.15 GB. Its clause table is about 4 bytes per literal, about 25M literals here.
- Stage 3's Linux CaDiCaL sizes matched the Mac's (2.6 GB mean, 3.9 GB max, against a 2.8 GB Mac peak).

Planning with up to 2 GB per worker, 90 workers need at most about 180 GB, and typically about 120 GB. Over all workers the 1.5 GB peak was rare.

**Instance type: c8g.24xlarge** (96 vCPU, 185 GiB, about US$0.445/h). Its memory is enough, and `MINFREE=8` holds back new cubes if it ever gets tight. m8g.24xlarge (370 GiB, about US$0.50/h) would only add cost. The 28 NMH encoder runs at the start take under 0.2 GB each.

**Budget:**

- Stage 4 is expected to cost about US$6, with a tail of about US$12–16.
- The per-box cap is US$25; with one resume box, at most US$50.
- That is well inside the US$100–120 set aside, and inside US$195 total with Stage 3 (about US$20–25) and stage12 (about US$8).

## 6. Launch and run (owner, from the repo root; `bash`, not zsh)

The plan is one c8g.24xlarge spot box with all 28 instances (`stage4`, 90 workers), started once stage12 has terminated, so that it sits next to the Stage 3 box inside the 192-vCPU spot quota. `launch.sh` defaults for `stage4*` are c8g.24xlarge, MaxPrice 0.60, cap US$25 (hard stop 2,490 min) and a 40 GB disk. Check the spot price first (`describe-spot-price-history`, c8g.24xlarge), as before; stage12 ran in eu-north-1b.

```bash
# 0. optional re-check (nothing is created)
bash scripts/cloud/launch.sh stage4 --az eu-north-1b --dry-run
# 1. launch, push code, build tools (~5-8 min)
bash scripts/cloud/launch.sh stage4 --az eu-north-1b          # prints INSTANCE_ID and IP
IP=<printed IP>
bash scripts/cloud/push.sh $IP
ssh -i ~/.ssh/kobon-aws.pem ubuntu@$IP 'cd tr && bash scripts/cloud/setup.sh'
# 2. start (fetches NMH's repo itself; if that fails: rsync -az -e "ssh -i ~/.ssh/kobon-aws.pem" refs/directed-ramsey-src ubuntu@$IP:tr/refs/)
ssh -i ~/.ssh/kobon-aws.pem ubuntu@$IP 'cd tr && nohup bash scripts/cloud/run_stage4.sh stage4 90 > results/stage4.log 2>&1 < /dev/null &'
# 3. Mac side (the cost meter already runs with --enforce --cap 195; do not start a second one)
nohup bash scripts/cloud/sync_back.sh $IP stage4 600 > results/stage4.sync.log 2>&1 &
bash scripts/cloud/watch.sh $IP stage4 900 120                 # exits on DONE, failure or stall
python3 scripts/stage4_progress.py                              # any time, on the synced results
# 4. at the end: results/stage4.DONE must be 0, and for every instance
#    results/stage4/<name>/run/summary.json must say ALL CLOSED (stage4_progress.py lists them)
```

The first minutes go to the 28 CNF builds, which run in parallel (`results/stage4/<name>.prep.log`; each must say "sha256 OK"). Then `results/stage4.log` shows one "conquer <name> with 15 workers" line per instance as it starts.

**Two boxes at once.** Use this only if both are free at the same time. It is not needed for the central projection. The split below is balanced by projected vCPU-h:

| Box | Stage name | Instances | Projected vCPU-h | Central / tail hours |
|---|---|---|---|---|
| 1 | `stage4-CFHIJKQRTUVXtw` | 23C, F, H, I, J, K, Q, R, T, U, V, X; ST26-p-TT5; ST25-p-W7 | 550 | 6.7 / 13.5 |
| 2 | `stage4-ABDEGLMNOPSWYh` | 23A, B, D, E, G, L, M, N, O, P, S, W, Y; ST25-p-H6 | 552 | 6.7 / 13.5 |

Run each box exactly as above, with its own stage name in `launch.sh`, `run_stage4.sh`, `sync_back.sh` and `watch.sh`. The result directories are disjoint.

**Resume after a spot reclaim or a hard stop.** Launch a new box with the same stage name (the cost meter adds its cost to that stage's cap), then `push.sh $IP`, `setup.sh`, and **`push.sh $IP --results-sub stage4`**. For one box of two, list only its own instances, e.g. `--results-sub stage4/23S-p-Y8 stage4/23H-p-Y8`. Then rerun the same `run_stage4.sh` command. Do not use `push.sh --results` here: it would put old copies of other stages' files on the box, and that box's `sync_back.sh` would copy them home over newer ones.

## 7. Stop rules

- **US$200 overall** (owner, 4 Nov 2026). `cost_meter.py --enforce --cap 195` terminates every running instance at US$195 total.
- **Per box: US$25** (`launch.sh` default for `stage4*`). The meter enforces it, and the user-data hard stop of 2,490 min fires first at the MaxPrice of 0.60.
- **Twice the projection: stop and report.** In `stage4_progress.py`, compare the "server h" total with the summed "proj vCPU-h" of the instances that are running or done. If it passes 2× before those instances close, stop the box (terminate it; the results are synced) and report. In box hours, one box should finish in about 13.5 h; at 27 h without DONE, stop and report.
- **Any SAT cube: stop and report.** The driver stops by itself and writes `results/stage4.SAT` with `verify_model.py`'s verdict. SAT would mean that NMH's UNSAT claim for that instance is wrong (if verify_model says "TT7-free OK"), or that a tool is broken (if it does not). Either way, nothing is resumed until the owner has looked.
- **Any "LRAT CHECK FAILED" line, or NOT CLOSED at the end.** Report it. A rerun retries the cube, but a repeated failure means a tool problem, not a mathematical result.
- **A sha256 mismatch in a prep log** (CNF built on the server differs from the Mac's): that instance is not run. Report it; do not edit the manifest to make it pass.
