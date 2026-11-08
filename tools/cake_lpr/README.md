# cake_lpr (formally verified LRAT/LPR proof checker)

The second proof checker of `scripts/audit/dualcheck.sh`, used on a sample of the pipeline's UNSAT results by `scripts/audit/cake_sample.py`.

- **Source:** https://github.com/tanyongkiam/cake_lpr (Yong Kiam Tan, Marijn Heule, Magnus Myreen), the release of 1 Nov 2026 (its final release), downloaded on 5 Nov 2026.
- **Upstream release:** all seven files here are byte-identical to the tag `cake_lpr/v1.0.0` (commit 033aad5, tagged 1 Nov 2026) of the cake_lpr repository (checked 8 Nov 2026 by SHA-256). Its README names HOL4 commit 9783a49 and CakeML commit 665f9b2 for the build; we did not rebuild from those commits.
- **What is verified:** the checker is verified in HOL4 and compiled by the verified CakeML compiler; `cake_lpr_arm8.S` is that compiler's ARMv8 output. Trusted, not verified: `basis_ffi.c` (the C wrapper: command line, file reads, heap allocation), the C toolchain, the OS and the hardware.
- **License:** `LICENSE` (CakeML's BSD 3-Clause terms).

## Files

Copied unchanged from the release. The x64 build `cake_lpr.S` is left out, so the `cake_lpr.S` line of upstream's `cake_lpr.sha256` has no file here.

| File | sha256 |
|---|---|
| `Makefile` | `5e001c7eafc88afc562f05aea80cbc86bad45a3335a0b57024dbe7c53beb5342` |
| `basis_ffi.c` | `bd498883fdc0577d734a771fe8197c5ff571f2abdd769b8dc95d46818db5cbbc` |
| `cake_lpr_arm8.S` | `50b63e18facbf1e6a814ab4bd5c9c9175d59ba3eb271286ffaabff5499c4852b` |
| `cake_lpr.sha256` | `10015b7fb26fe1be1b3665edf3eb393e3f5a9b125410b33a6e4ac8d8ccf8781e` |
| `LICENSE` | `251cdc54d59eb4d22a0969b78714b3baef76724744b3c90e73a83cc63374a18a` |
| `example.cnf` | `b91a7a8e0718672619fdee1a27a216afcde571a567dd29fda2cf2b84a4a13887` |
| `example.lpr` | `1d9be4845ecf4b0e8bfa4a92ecc4b3f9543ad86892a6e55a0d1831ff120630e9` |

The first three equal the values in upstream's `cake_lpr.sha256`; `scripts/audit/cake_build.sh` checks them before every build.

## Build and self-test

`bash scripts/audit/cake_build.sh` (also a step of `scripts/cloud/setup.sh`):

1. checks the sha256 values;
2. runs `make` here (it picks `cake_lpr_arm8.S` on arm64 and aarch64) and moves the binary to `build/cake_lpr`;
3. fails unless the example proof gives exactly `s VERIFIED UNSAT`, and the following are rejected: the bogus proof `3 0 0` (an empty clause without a conflict) of the satisfiable `1 2 / -1 2`, an empty proof, and the example proof cut short.

## Behaviour (measured 5 Nov 2026 on the Mac)

**Usage.** `cake_lpr [--CML_HEAP_SIZE=MiB] [--CML_STACK_SIZE=MiB] FORMULA PROOF`.

- The wrapper removes the two flags wherever they appear, before or after the file names. Both orders were tested.
- The defaults are 4096 MiB each. A bad value prints `CakeML: invalid ...` and exits 3.

**Input.** It reads CaDiCaL's text LRAT (`--lrat=true --binary=false`).

- Each file is read once, front to back, to the end. Named pipes and `/dev/fd/N` pipes work for both the formula and the proof.
- Lines after the empty clause are read too: a proof followed by 50 MB of deletions still verified.

**Verdict.** Only the output is a verdict, because cake_lpr exits 0 even when the check fails.

- On success, stdout is exactly `s VERIFIED UNSAT` and stderr is empty.
- Failures go to stderr with exit 0, for example:
  - `c Checking failed at line: 0. Reason: pivot must be non-zero` (an empty clause without a conflict);
  - `c Checking failed at line: 0. Reason: failed to parse line (uncompressed format)`;
  - `c empty clause not derived at end of proof`;
  - `c Input file: X no such file or directory`.
- Heap exhaustion prints `CakeML heap space exhausted.` and exits 1.
- `dualcheck.py` therefore counts cake_lpr as VERIFIED only on exit 0 with exactly that one stdout line and an empty stderr.

**Memory.** The resident size grows to the whole heap: peak RSS equalled `--CML_HEAP_SIZE` in every run on a real formula. The heap therefore *is* the memory cost per process.

The smallest heap that works is set by parsing the formula. On both Stage 4 cubes, the proof needed no more heap than the formula alone.

Smallest working heap with a one-line proof (formula only), bisected to 32 MiB:

| Formula | Clauses | DIMACS bytes | Fails at | Works at | Heap per byte |
|---|---|---|---|---|---|
| `cnf/stage4/ST26-p-TT5.cnf` | 1,099,282 | 48.1 MB | 576 MiB | 608 MiB | 12.6–12.9 |
| `cnf/stage4/23A-p-Y8.cnf` | 2,353,250 | 105.1 MB | 1248 MiB | 1280 MiB | 12.5–12.8 |
| Stage 3 `24A-p-O21s.tri.cnf`, first 0.5M clauses | 500,000 | 55.5 MB | 576 MiB | 608 MiB | 10.9–11.5 |
| Stage 3 `24A-p-O21s.tri.cnf`, first 1.0M clauses | 1,000,000 | 115.3 MB | 1152 MiB | 1184 MiB | 10.5–10.8 |

**Speed.** Measured with nice 10, files on disk:

| Run | CaDiCaL | lrat-check | cake_lpr |
|---|---|---|---|
| 23A-p-Y8 level-0 cube 23 (64 MB proof, 2.94M clause ids) | 11.4 s, 0.98 GB | 1.40 s, 0.15 GB | heap 1024: exhausted after 26 s; 1280: smallest that works; 1536: 6.9 s; 2048: 5.5 s; 2560: 5.2 s |
| ST26-p-TT5 level-0 cube 520 (125 MB proof) | 55 s, 0.57 GB | 1.47 s, 0.09 GB | 608 MiB: smallest that works; 1024: 4.5 s; 1536: 4.2 s |
| Formula alone, 23A-p-Y8 | – | 1.06 s | 3.5 s (heap 2048) |

Above about 1.5 times the smallest heap, more heap barely helps.

**Streamed** through `scripts/stream_solve.py` (CaDiCaL, then the checker over named pipes):

| Cube | lrat-check alone (wall / CPU) | `dualcheck.sh` (wall / CPU) |
|---|---|---|
| ST26-p-TT5 cube 520 | 40.8 s / 42.1 s | 42.7 s / 48.5 s |
| 23A-p-Y8 cube 23 | 11.2 s / 11.6 s | 14.9 s / 18.3 s |

The extra wall time is mostly cake_lpr parsing the formula, while CaDiCaL waits on the full proof pipe. After that, cake_lpr checks about 30 MB of proof per second, far more than CaDiCaL writes (2–6 MB/s), so it does not hold CaDiCaL back.

## Extrapolation (not measured)

The assumption: the smallest heap grows linearly with the formula. It does on the two Stage 3 prefixes (592 MiB → 1168 MiB from 0.5M to 1.0M clauses, about 16 MiB fixed). The proof needs no more than the parse, as on the two Stage 4 cubes.

**Stage 3**, one `24X-p-O21s` instance: 9,007,047 clauses, 209M literals, 504 free arcs, 1,071 MB.

- The smallest heap is about 10.2–11.1 GiB: 16 + 1.152 MiB × 9,007 thousand clauses = 10,392 MiB, or 10.5–10.9 bytes per byte.
- `cake_sample.py --heap auto` gives 1.25 × 12.9 bytes per byte = 16,640 MiB (16.3 GiB resident), about 1.5 times that minimum.
- Add CaDiCaL (2.6 GB mean, 3.9 GB max per Stage 3 cube in run 1) and lrat-check (about 6.8 bytes per literal on 23A-p-Y8, so about 1.4 GB). That is **about 20–22 GiB per worker**.
- On 370 GiB, at most 16 workers; 15 leaves a margin.
- Parsing the 1.07 GB formula takes about 35 s on the Mac (3.3 s per 100 MB), probably about a minute on the server, per item.
- Not measured: the heap that the much longer Stage 3 proofs need beyond the parse. The headroom covers it, and an exhausted heap is reported (`cake_heap_exhausted` in the summary), not hidden.

**Stage 4**, NMH's instances: 2.2–2.6M clauses, 98–116 MB.

- The smallest heap is 1.2–1.5 GiB. Auto gives 1792 MiB; ST26-p-TT5 gets the 1024 MiB floor.
- With CaDiCaL (up to 1.5 GB) and lrat-check (0.15 GB), that is **about 3.4 GiB per worker**. CPU, not memory, limits the worker count.

**Enumeration jobs** (k = 6: 2.8–12 MB per job formula): the 1024 MiB floor, about 1 GiB per worker.
