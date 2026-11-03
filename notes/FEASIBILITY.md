# Proving R(7) ≤ 46 for tournaments: feasibility study

Date: 3 Nov 2026. Planning only: no cloud compute was used. Local experiments ran on an Apple M5 (10 cores, 16 GB, shared) at `nice 10` and took about 1.95 CPU-hours.

Notation:

- R(k) is the least n such that every tournament on n vertices contains a transitive subtournament TT_k.
- `X -p- Z` is a pivot instance. A vertex p has in-neighbourhood X and its out-neighbourhood contains Z. The arcs inside X and inside Z are fixed. All X×Z arcs are free.
- The question an instance asks is: "is there a TT7-free completion?" UNSAT means no such completion exists.

NMH stands for Neiman, Mackey and Heule, "Tighter bounds on directed Ramsey number R(7)", [arXiv:2011.00683](https://arxiv.org/abs/2011.00683) v2 (18 May 2022). The journal version is *Graphs and Combinatorics* 38, 156 (2022), [doi:10.1007/s00373-022-02560-5](https://doi.org/10.1007/s00373-022-02560-5).

## 0. Verdict: go, with conditions

The problem is much smaller than our 2 Nov sketch assumed. Two public 2022 TT6-free catalogues and NMH's own UNSAT runs together reduce R(7) ≤ 46 to the following:

1. **Two catalogue facts, still to be verified independently:**
   - **S22:** every TT6-free tournament on 22 vertices contains Y8.
   - **S21:** every TT6-free tournament on 21 vertices contains Y8, or is isomorphic to one specific tournament O21*.

   Both hold for the 2022 files in `evanlohn/digraph_isolators` (89 and 17,040 classes). Those files carry no method and no completeness claim.
2. **Five further SAT instances,** `I24X -p- O21*` for X = A, …, E. Each has all 46 vertices, with only the 504 X×O21* arcs free. A SAT answer would be a TT7-free tournament on 46 vertices, which would mean R(7) = 47. So these are almost certainly UNSAT. What we do not know is how hard they are.

The (23,22) split needs **no new SAT run** once S22 is confirmed. NMH's 25 UNSAT runs `I23 -p- Y8` already exclude it.

Conditions for spending money:

- **(a)** Re-enumerate the TT6-free tournaments on 22 vertices, and then on 21, from the TT5-free catalogue by pivot decomposition. Compare the result with the Lohn files. Estimated at 100 to 2,000 vCPU-hours, likely nearer the low end.
- **(b)** Before any long AWS run, a better cube-and-conquer estimate for the five instances must project at most about 6k vCPU-hours, or 12k if Stage 4 is dropped (§4.4, §6).
  - Today's crude split of `I24A -p- O21*` gives a central estimate of about 1,600 vCPU-hours (US$8.5) for all five.
  - The range is US$2–37, with a tail risk of about US$80.
- **(c)** State the result as resting on NMH's published computations. Their 27 long runs (about 4,800 CPU-hours in 2020–22) published no DRAT or LRAT proofs. Re-running them with proofs is optional (Stage 4) and fits only if Stage 3 is cheap.

## 1. Rival status as of 3 Nov 2026

The search covered arXiv, Semantic Scholar and OpenAlex citations, GitHub, Zenodo, OEIS, V3R1T4S, erdosproblems.com, Epoch and other open-problem lists, McKay's data pages, and web search. Raw responses are under `refs/rival/` (gitignored, not redistributed).

**Nothing found improves 34 ≤ R(7) ≤ 47, and no visible R(7) work has appeared since 2022.**

| Source | Finding |
|---|---|
| arXiv:2011.00683 | Still v2. The journal version (G&C 38:156, online 9 Sep 2022) keeps the same bounds. Its accepted manuscript ([par.nsf.gov 10392661](https://par.nsf.gov/servlets/purl/10392661)) adds the Lohn et al. extra 33-vertex tournament and an encoding note. The Springer page itself was not readable from here. |
| Lohn, Lambert, Heule, "Compact Symmetry Breaking for Tournaments", FMCAD 2022 ([pdf](https://www.cs.cmu.edu/~mheule/publications/FMCAD22.pdf)) | The only citing work that does R(7) computation. Kissat on 640 cores found one new self-complementary TT7-free 33-vertex tournament. All 5303 previously known ones contain ST26, and 4952 contain ST27. No bound changed. The paper does not mention the TT6-free catalogues below. |
| [github.com/evanlohn/digraph_isolators](https://github.com/evanlohn/digraph_isolators) (last push 25 Oct 2022; files committed 25 May 2022) | `tt6free_tournaments/tt6free{20..27}.d6` contain 88,410 / 17,040 / 89 / 25 / 5 / 1 / 1 / 1 TT6-free tournaments. No method or completeness claim is stated. **This is the key input for this study (§3).** |
| [neimandavid/Directed-Ramsey](https://github.com/neimandavid/Directed-Ramsey) (last push 14 Apr 2022) | NMH's code, catalogues and solver logs. No later activity and no forks. |
| McKay, `ramsey.html` | `tt7free33some.d6` holds 5305 TT7-free 33-vertex tournaments (file of 5 Nov 2022). The page says "there may be more", none extends to 34, and the maximum TT7-free order is 33 to 46. It has no TT6-free counts by order. |
| OEIS [A122026](https://oeis.org/A122026) | Data 0,1,2,4,8,14,28. Revision 9 (14 Nov 2019) is the latest; we re-checked via the JSON API today. No a(7) bounds and no citation of NMH. |
| erdosproblems.com | #1216 (Erdős–Moser, asymptotic, marked disproved, Apr 2026 comments) and #112 (a different function) say nothing about R(7). |
| V3R1T4S (`bank/targets.json`, 1104 targets, 30 Oct 2026) | No R(7), directed-Ramsey or TT_k target. |
| Epoch FrontierMath Open Problems; google-deepmind formal-conjectures; Justin Sun Prize list | No R(7). JSP-001021 (Lean, small cases such as R(6) = 28) is marked solved, and its issue #1246 says it does not address R(7). formal-conjectures PR #6268 (open, 30 Oct 2026) has no R(7) statement. |
| Other 2022–26 arXiv | McCarthy–Monico (EJC 2025) give lower bounds for other R(m) and cite R(7) ≥ 34. Li–Duggan–Bright–Ganesh (IJCAI 2025) only restate R(7). Lidický–Pfender's SIAM Review SIGEST (2026) republishes the 2021 SDP paper (R(7) ≤ 53); its text was not readable here. |

Not checked:

- Google Scholar (it blocks bots).
- The Springer full texts of NMH and of Sanchez-Flores 1994 and 1998.
- The SIAM SIGEST text.
- GitHub code search (needs login).
- zbMATH and MathSciNet.
- Theses and talks beyond web search.

**Scoping.** We found no prior statement of the reduction in §3. That is a finding of this search, not proof that nobody has made the observation.

## 2. What the R(7) ≤ 47 proof did (NMH)

### 2.1 Statements

1. All TT6-free tournaments on 24 and 25 vertices are subtournaments of ST27 (Sanchez-Flores' conjecture). That gives 5 classes on 24 vertices (24A–24E) and 1 on 25 (ST25).
2. There are exactly 25 TT6-free tournaments on 23 vertices: 22 sub-ST27 classes (23A–23V) and 3 doubly regular ones (23W, 23X and 23Y = QR(23)).
3. 34 ≤ R(7) ≤ 47.

Facts used from Sanchez-Flores (1994, 1998; abstracts only checked): R(6) = 28, ST27 is unique, ST26 is unique, and every tournament on 54 vertices contains TT7.

### 2.2 How the classifications were proved

- Fix an arc u→v. Split the remaining vertices into blocks A (common out), B (u→w→v), C (common in) and D (3-cycles with uv).
- A, B and C are TT4-free, so each has at most 7 vertices. Averaging 3-cycles over arcs gives |D| ≤ 6.
- A brute-force search in Matlab with propagation handled 7 block-size cases on 24 vertices and 9 on 23. The runs took between 12 hours on a laptop and about a week with 16 workers.
- The case [5,5,5,6] on 23 vertices reduces to doubly regular tournaments, taken from McKay's list (37 tournaments, 3 of them TT6-free).
- The case [7,3,7,4] on 23 vertices is a CaDiCaL UNSAT in minutes. The authors note that shrinking any block makes it SAT, which is why they expected a 22-vertex catalogue to be expensive.

### 2.3 Upper bound

R(6) = 28 bounds every in-degree by 27, and reversing all arcs swaps in- and out-degrees.

- **In-degree ≥ 26 ⇒ out-degree ≤ 13.** `ST26 -p- TT5` is UNSAT, and R(5) = 14.
- **In-degree 25 ⇒ out-degree ≤ 19.**
  - Lemma: every tournament on ≥ 10 vertices contains TT5, H5 or G6. So every tournament on ≥ 20 vertices contains TT6, H6 or G7.
  - Here H6 is TT3 ⇒ C3, and G7 (called "W7" in their files) is TT2 ⇒ regular 5-tournament.
  - `ST25 -p- H6` and `ST25 -p- W7` are UNSAT. Their logs give 23.9 h (88.2M conflicts) and 33.5 h (95.7M conflicts).
- **In-degree 23 ⇒ out-degree ≤ 22.**
  - Y8 is an 8-vertex tournament with 15 three-cycles that lies in all 25 TT6-free 23-vertex tournaments.
  - All 25 instances `I23 -p- Y8` are UNSAT. Each has 32 vertices, 184 free arcs, 5456 variables and 2.2–2.36M clauses.
  - They took 14.5 to 431.6 CPU-hours each (mean 190, median 204), 4,743 hours and 1.0·10^10 conflicts in total.
  - They ran with CaDiCaL 1.2.1/1.3.1 in June 2020 on AWS m5d.16xlarge machines, one solver per vCPU. The ST25 runs used CaDiCaL 1.5.2 in March 2022 with `--stabilize=false --walk=false`.
- **Parity closes 47.** Only in-degrees 22 and 24 remain, both even, but C(47,2) = 1081 is odd.
- **Why they stopped at 47.** For n = 46, (in, out) = (24,21) and (23,22) both survive and parity no longer helps. Their Future Work says a TT6-free catalogue above about 20 vertices "could likely be used to further reduce the upper bound".

### 2.4 Encodings

- **Variables.** One variable per arc, true when the arc points from the lower index to the higher. No cardinality constraints and no symmetry-breaking predicates; symmetry is broken only by fixing X and Z.
- **Three TT_k exclusions were tried:**
  - the naive form, one clause per ordering;
  - a 3-cycle form, with an auxiliary c_uvw → cycle and one clause per k-set over its C(k,3) triangles;
  - orderings reduced by self-subsuming resolution. This form is arc-consistent and was best in most of their runs.
- **What `encoding/tour-encode.c` does.** For each k-set it skips the set if it contains a fixed 3-cycle. Otherwise it uses reduced direct clauses when at most `limit` orderings are compatible, and the triangle clause otherwise.
  - The ST25 instances are direct only (496 variables).
  - The Y8 instances use triangle variables.
- **No proofs.** Their repo has the inputs, the C encoders and the 27 logs. No DRAT or LRAT proofs were published.

We rebuilt their exact `ST25-p-H6` CNF with their encoder. It has 1,687,063 clauses and 74,752,227 bytes, identical to the counts in their log.

## 3. Case list for n = 46

Let T be TT7-free on 46 vertices and v any vertex, so d⁻(v) + d⁺(v) = 45. Both N⁻(v) and N⁺(v) are TT6-free.

### 3.1 Exclusions from NMH's results

1. **d⁻ ≥ 26 is impossible.** N⁻ contains ST26 (unique). d⁺ ≥ 18 ≥ 14, so N⁺ contains a TT5. That contradicts `ST26 -p- TT5` being UNSAT.
2. **d⁻ = 25 is impossible.** N⁻ is ST25 (unique, NMH). N⁺ has 20 vertices, so it contains TT6, H6 or W7. TT6 is impossible because N⁺ is TT6-free. Both `ST25 -p- H6` and `ST25 -p- W7` are UNSAT.
3. **Reversal.** By reversal, d⁺ ≤ 24, so d⁻ ∈ {21, 22, 23, 24}.

The splits are therefore (24,21), (23,22), (22,23) and (21,24). Reversing all arcs maps (a,b) to (b,a). It suffices to exclude in-degree 24 and in-degree 23.

**Our 2 Nov sketch was right on this point.** Counting does not close either case alone. With all in-degrees in {22, 23}, or all in {21, 24}, the in-degrees can still sum to 1035 = C(46,2), with 23 vertices of each value.

### 3.2 (23,22): closed by existing results once S22 holds

N⁻(v) is one of the 25 tournaments on 23 vertices. N⁺(v) = O22 is TT6-free on 22 vertices. If Y8 ⊆ O22, then `I23 -p- Y8` is a sub-configuration, and NMH proved it UNSAT.

We checked all 89 tournaments in `tt6free22.d6`. All contain Y8, and all contain reversed Y8. So if that file is complete, (23,22) and, by reversal, (22,23) are excluded **with no new computation**.

### 3.3 (24,21): reduces to five instances once S21 holds

N⁻(v) = I24X with X ∈ {A, …, E}, and N⁺(v) = O21. Suppose Y8 ⊆ O21. Take any 23-vertex I23' ⊂ I24X. It is TT6-free, so it is one of NMH's 25. Then `I23' -p- Y8` is a sub-configuration, which is UNSAT.

Of the 17,040 tournaments in `tt6free21.d6`, 17,039 contain Y8. The one exception, **O21***, has these properties:

- regular (all out-degrees 10), with 385 three-cycles, the maximum;
- automorphism group of order 63, vertex-transitive and self-converse;
- contains neither Y8 nor reversed Y8;
- contains H6 but not W7;
- not a subtournament of ST27, of the three doubly regular 23-vertex tournaments, or of any of the 89 tournaments on 22 vertices.

It is saved as `data/O21star.txt`.

So, given S21, (24,21) and (21,24) reduce to five instances, `I24X -p- O21*` for X = A–E.

### 3.4 Why the catalogue route is needed

The NMH style, with small forced structures and no catalogue, fails for (24,21). `I24X -p- H6` is **SAT** for X = A, B and C; each model was checked independently to be TT7-free. `I23A -p- H6` is SAT too. Of the forced pair {H6, W7}, H6 alone already fails.

We also tried the "fewest 3-cycles" subtournaments Z8, Z10 and Z12 of O21* (`I24 -p- Zm`). They gave no answer in 60 s. They remain an option if the full instance proves hard (§6, Stage 3a).

### 3.5 Corrections to the 2 Nov sketch

1. The degree range 21–24 is correct.
2. The sketch's plan was to catalogue TT6-free tournaments on 18–24 vertices and pair neighbourhoods. That is unnecessary: catalogues for 20–27 vertices already exist (unverified), and (23,22) needs no pairing at all.
3. The whole new SAT workload is five instances, plus re-verifying the catalogues.

### 3.6 Consistency of the Lohn files

All checks below were run by us (`scripts/e5_lohn_catalogue.py` and `e9_closure.py`):

- Every member is a tournament, TT6-free and pairwise non-isomorphic under nauty.
- Each file is closed under reversal.
- The self-converse counts match the `_sc` files.
- The n = 23 and n = 24 files equal NMH's classes, and the n = 25 to 27 files are ST25, ST26 and ST27.
- The 22-vertex subtournaments of the 25 tournaments on 23 vertices are exactly the 89.
- The 21-vertex subtournaments of the 89 form 305 classes, all present in the 17,040.

These are necessary conditions for completeness, not a proof of it.

## 4. Measurements (this Mac)

All runs are logged in `results/runs.csv`, with logs under `results/logs/`. Tools: CaDiCaL 3.0.1, Kissat 4.0.4, nauty 2.8 and march_cu (built from the kobon CnC sources).

### 4.1 Encoder validation

| Check | Result |
|---|---|
| ST27 built as Paley(GF(27)) | Isomorphic to NMH's ST27, TT6-free (largest TT is 5), self-converse |
| Sub-ST27 classes on 26 / 25 / 24 / 23 / 22 vertices | 1 / 1 / 5 / 22 / 82. The 24 and 23 sets equal NMH's 24A–E and 23A–V. |
| QR(23) | TT6-free, isomorphic to 23Y |
| Y8 | The same in all 25 NMH logs and contained in all 25 tournaments on 23 vertices. It has 15 three-cycles and is not self-converse. |
| `build/encode` against brute force | 74,944 assignments of random partial tournaments (n = 8–10, k = 4–5, direct and triangle modes): 0 mismatches |
| NMH encoder, reproduced | `ST25-p-H6` CNF byte count and clause count identical to their log |
| R(5) ≤ 14 as pivot `ST6 -p- ST7` | UNSAT, 75 conflicts, **LRAT VERIFIED** (lrat-check) |
| `ST6 -p- ST6` | SAT (the 13-vertex TT5-free tournament exists) |

### 4.2 What plain CDCL cannot do

These runs are why the pivot and catalogue structure matters:

- TT5-free on 14 vertices, all arcs free: UNKNOWN after 290 s (6.1M conflicts). Its LRAT proof reached 1.8 GB in 290 s.
- TT6-free on 27 vertices, all arcs free: UNKNOWN after 177 s. On 28 vertices: UNKNOWN after 174 s.
- **TT6-free on 22 vertices, all arcs free:** UNKNOWN after 114 s with CaDiCaL and after 120 s with Kissat.
- In the pivot form `A -w- B`, with A and B from the TT5-free catalogue and 99–110 free arcs, 16 random 22-vertex instances took 5.2 s each on average: 14 UNSAT, 1 SAT (contains Y8, extends to a known 23), and 1 still running at 20 s.
- `ST26 -p- TT5` (NMH 5.2.1) with LRAT logging: UNKNOWN after 582 s and 1.8M conflicts. It is not "easy".
- Two other ways to sample TT6-free 22-vertex tournaments both failed:
  - Fixing 40 random arcs and calling the SAT solver gave no sample in about 10 CPU-minutes.
  - A random walk by single-arc reversal from QR(23) minus a vertex accepted 0 of 3000 reversals: every reversal created a TT6. These tournaments are locally rigid.

### 4.3 Calibration against NMH's logs

- We ran their exact `ST25-p-H6` CNF with their options for 582 s: 1,462,103 conflicts, or 2,512 per second.
- Their m5d run had reached 990k conflicts by 539 s, or about 1,840 per second.
- So one M5 core with CaDiCaL 3 gives about 1.4× their conflict rate. At equal conflict count their 23.9 h would be about 9.8 h here.

### 4.4 The instances that matter

| Instance | Vars (free arcs) | Clauses | Result |
|---|---|---|---|
| `I24X -p- H6`, X = A–E | 144 | 1.67M | **A, B, C: SAT** (model verified). D, E: unknown at 60 s. |
| `I24X -p- W7`, X = A–E | 168 | 2.58M | unknown at 60 s |
| `I23A -p- H6`; `I23{A,W,Y} -p- {H6,W7}` | 138 / 161 | 1.3–2.1M | 23A-p-H6 SAT (model verified); the rest unknown at 30 s |
| `I24{A,B} -p- Z8 / Z10 / Z12` | 192 / 240 / 288 | 4.5M / 8.9M / 1.6M (Z12 triangle encoding) | unknown at 60 s |
| **`I24A -p- O21*`** (all 46 vertices) | **504** | 9.0M clauses, 209M literals (triangle encoding; the prime direct encoding would be 95.6M clauses) | **unknown at 296 s** with LRAT logging; 1.1M conflicts, 4.6 GB RSS, LRAT at 1.9 MB/s |

Static-split estimates (`scripts/split_estimate.py`) fix the 10 most frequent arc variables. That gives 1024 pieces, and we sampled pieces with a per-piece time limit:

- **`ST25-p-H6`, used as calibration:** 6 pieces, all UNSAT, mean 4.8 s (about 2 s of which is parsing). The estimate is about 1.4 CPU-hours, against NMH's 23.9 h for one monolithic run. Splitting pays off strongly on these formulas.
- **`I24A -p- H6`:** 8 pieces gave 4 UNSAT (1.1–46 s), 1 SAT, and 3 still unknown at 60 s.
- **`I24A -p- O21*`:** we split on the 10 most frequent arc variables (all of them the arcs from one vertex of I24A into O21*) and sampled 10 of the 1024 pieces, from two seeds.
  - 4 pieces were UNSAT, in 5.0, 5.1, 54 and 60 s.
  - We re-ran one of them with LRAT. The proof was 5.8 kB and **VERIFIED** in 7.7 s, so the LRAT pipeline works at the full 9M-clause size.
  - The other **6 pieces were still unknown at 120 s**.
  - Counting each unknown piece as 120 s gives a lower bound of 1024 × 84 s ≈ **24 M5-core-hours** for this one instance under a naive split.
  - The true cost depends on the unknown pieces. We ran one of them to the end: **UNSAT in 351 s** (919k conflicts).
  - If the unknown pieces average 3–15 minutes, `I24A -p- O21*` costs about **33–155 M5-core-hours (central estimate ~65)** with this naive split.
  - Symmetry is unused so far. Aut(O21*) has order 63, and |Aut(I24X)| is 9, 1, 1, 3 and 3 for A–E, so the cross-arc assignments fall into orbits of size up to 567 (A), 63 (B, C) and 189 (D, E).

march_cu lookahead cubing at depth 10 on the 2M-clause `ST25-p-H6` gave no cubes within 8.2 CPU-minutes, and we stopped it. On these clause-heavy formulas, cubing on arc variables, or with a cheaper lookahead, is preferable.

## 5. Compute estimate

Cost assumptions:

- Graviton4 spot at about 192 vCPU per US$1/h, as given. That makes about US$0.0052 per vCPU-hour and roughly 19k vCPU-hours for the US$100 budget.
- One Graviton4 vCPU is taken as 0.6–0.8 of an M5 performance core for CaDiCaL, which puts it at about 1–2× an m5d vCPU of 2020–22. This ratio is unmeasured.

| Stage | Work | vCPU-h (range) | US$ |
|---|---|---|---|
| A0 | Verify the TT5-free catalogue for n ≤ 13 (gentourng 10, then extend) | < 2 | ≈ 0 |
| A1 | Re-enumerate the 22-vertex tournaments, S22: 17,673 pivot instances (vertex of maximum out-degree d ≥ 11; (\|A\|,\|B\|) = (10,11), (9,12), (8,13)), AllSAT. Measured about 5 s per instance with a tail. | 30–150 | 0.2–0.8 |
| A2 | Re-enumerate the 21-vertex tournaments, S21: about 168k pivot instances (d = 10 forces a regular tournament; d = 11–13), AllSAT with max-degree constraints | 200–2,000 | 1–10 |
| A3 | One-vertex extensions 22 → 23 → 24 → 25: an independent cross-check of NMH's classifications | < 20 | ≈ 0 |
| B / 3 | Five instances `I24X -p- O21*`, with cube-and-conquer and LRAT per cube (checking included) | **400–7,000 (central ~1,600); tail risk up to ~15,000** | **2–37 (central ~8.5); tail up to ~80** |
| C / 4 (optional) | Re-run NMH's 27 long instances with CnC and checked LRAT. They took 4,800 m5d-hours; solving plus checking is estimated at 2× that, scaled to Graviton4. | 5,000–10,000 | 26–52 |

**How the Stage 3 range was derived.** Five instances at 33–155 M5-core-hours each (central ~65) gives 160–780 core-hours. That is multiplied by:

- 1.25–1.7 for a Graviton4 vCPU compared with an M5 core;
- about 2.2 for LRAT logging plus streaming checks;
- 1–2.4 for memory packing. Each solver needs 4.6 GB, so only about 80 fit on a 384 GB, 192-vCPU box unless the encoding shrinks.

The tail case covers pieces that take hours. Instances B–E were not measured. Symmetry breaking under Aut(O21*) × Aut(I24X) and lookahead cubing should lower these figures, but by an unmeasured amount.

**Proof storage is a hard constraint.** Text LRAT was measured at 2–6 MB/s per process. A 190-hour run would produce several TB. Every long run must therefore be cubed into pieces of at most about 30 minutes. Each piece's LRAT is checked as it is produced (lrat-check or cake_lpr) and then deleted. We keep only the cube list, a check that the cubes cover the space, and per-cube hashes.

## 6. Staged plan with go/no-go checkpoints

**Stage 0 — Mac, at most 1 day and about 8 CPU-hours.**

1. Build the pivot AllSAT enumerator: CaDiCaL incremental through its C++ API with blocking clauses, or a dedicated backtracker, with canonical forms from nauty.
2. Build the CnC pipeline: arc-variable cubes, CaDiCaL with `--lrat` per cube, streaming lrat-check, and a cube-coverage check.
3. Verify the TT5-free catalogue for n ≤ 13.
4. Time A1 on a random 2% of its pivot instances.

**Go/no-go 0:** the A1 projection must be at most 300 vCPU-hours.

**Stage 1 — AWS, one 192-vCPU spot box, a few hours, about US$1.** Run A1 and A3.

**Go/no-go 1:**
- Exactly 89 classes, all containing Y8, closes (23,22) modulo NMH.
- Any extra class without Y8 means adding instances `I23 -p- O22'`, 25 per new class, and re-planning.
- Any disagreement with NMH's classification on 23–25 vertices means stopping and reporting it.

**Stage 2 — AWS, up to about US$10.** Run A2.

**Go/no-go 2:** the Y8-free set must be {O21*}. Each additional Y8-free class adds 5 instances to Stage 3.

**Stage 3 — the five instances.**

- **3a, Mac, at most 4 CPU-hours.** Pick a split per instance: arc-variable cubes of depth 12–16, aiming for pieces of 1–10 minutes. Sample 30 pieces per instance. Also try (i) Aut(O21*) of order 63, together with Aut(I24X), to break symmetry on the cube variables, and (ii) the smaller sub-structures Z12–Z16 of O21*, whose UNSAT would imply the full instance's UNSAT.
- **Go/no-go 3:**
  - At most 6,000 vCPU-hours projected for all five: run on AWS.
  - 6,000–12,000: run only if Stage 4 is dropped.
  - Above 12,000: stop, publish Stages 1–2, and rethink the encoding.
- **3b, AWS.** Run the cubes with streaming LRAT checks.
  - Any SAT piece is checked independently with `scripts/verify_model.py` (no TT7 on 46 vertices). That would show R(7) = 47; this is very unlikely.
  - All pieces UNSAT, with a valid cover, gives R(7) ≤ 46, conditional on NMH.

**Stage 4 — optional, only with at least US$40 left.** Re-verify NMH's 27 instances (ST26-p-TT5, ST25-p-{H6,W7} and 25 × I23-p-Y8) with checked LRAT. The result then rests on no unchecked computation, apart from the TT5-free base catalogue, which Stage 0 verifies.

**Stop rules.**
- Hard cap of US$100.
- Any stage that exceeds twice its projection stops and reports.
- No AWS resource starts before go/no-go 0 and an explicit owner OK.

## 7. Honest probabilities

These are subjective estimates; the evidence for each is given.

- **S21 and S22 hold, so the Lohn files are right on the Y8 facts:** about 0.9. The files agree with every published classification and pass every closure and consistency check we ran. Their provenance and method are undocumented.
- **The five instances are UNSAT:** at least 0.98. SAT would mean R(7) = 47. Against that: 5305 TT7-free tournaments are known on 33 vertices and none extends to 34.
- **The five instances can be solved within the remaining budget:** about 0.75. The evidence is 10 sampled pieces of one instance out of five, one finished 'hard' piece at 6 minutes, and symmetry plus better cubing still unused. The risk is a heavy tail of pieces that take hours.
- **A complete proof of R(7) ≤ 46 within US$100, conditional on NMH's computations:** about 0.6, which is 0.9 (catalogues) × 0.95 (enumeration works) × 0.75 (Stage 3) × 0.98 (UNSAT) ≈ 0.63. With every long computation re-checked by LRAT (Stage 4 included): about 0.35–0.4.
- **Publishable intermediate results:** about 0.7. These would be an independent, checked enumeration of the TT6-free tournaments on 21 and 22 vertices, the Y8 reduction (§3.2–3.3), and the negative result that H6 alone does not close (24,21). As a stand-alone note this is modest. It is strongest as part of the full result.

## 8. Risks

- **Catalogue completeness (the main conditional).** Mitigated by Stages 1–2, which also cross-check NMH's classifications on 23–25 vertices.
- **Unchecked NMH computations.** They used Matlab classification, CaDiCaL 1.2–1.5 runs and no proofs. They are peer-reviewed but unchecked. Mitigated by A3 and the optional Stage 4.
- **Stage 3 hardness is the main cost risk.** We found no report of instances like these: 504 free arcs and 9M clauses, with both neighbourhoods fully fixed. One 5-minute monolithic run plus 10 sampled pieces of one instance (§4.4) are thin evidence. A heavy tail of pieces taking hours would break the budget.
- **Memory.** The full instance needs 4.6 GB per solver. On a 192-vCPU box (c8g.48xlarge has 384 GB) that allows at most about 80 concurrent solvers, not 192, unless the encoding shrinks (for example by symmetry reduction or a smaller Z), or a memory-heavier instance type is used. Throughput per dollar then falls by up to about 2.4×. The Stage 3 range includes this factor.
- **Proof volume.** Only streaming checks are feasible.
- **Encoding bugs.** Mitigated by exhaustive small-case tests, byte-for-byte equality with NMH's encoder on their instance, LRAT checks, and independent model checks.
- **Spot interruptions.** Mitigated by cube-level checkpoints.
- **Shared Mac.** All local work stays at `nice 10` with at most 3 parallel jobs.

## 9. Reproduce

```bash
scripts/fetch_refs.sh                 # third-party PDFs, repos (gitignored; SHA256 in refs/SHA256SUMS.txt)
cc -O2 -o build/encode src/encode.c   # our encoder; tests: python3 tests/test_encode.py
python3 scripts/e1_catalog.py && python3 scripts/make_data.py
python3 scripts/e5_lohn_catalogue.py && python3 scripts/e9_closure.py 23 22
python3 scripts/e7_zsubsets.py
scripts/batch_validation.sh; scripts/batch_46_quick.sh; scripts/batch_46_z.sh
python3 scripts/split_estimate.py <name> <cnf> --k 10 --samples 8 --limit 60
python3 scripts/verify_model.py cnf/mat/24B-p-H6.txt cnf/24B-p-H6.cnf
```

Instance matrices are built in `cnf/mat/` by `src/instances.py` (see `results/e*.json`). The CNFs are regenerated by `build/encode MATRIX 7 LIMIT OUT.cnf`, with LIMIT = 5900 for the direct encoding and 1 for the triangle encoding.

## 10. What this study did not do

- It did not verify the completeness of any catalogue.
- It did not re-run any NMH long instance beyond a 10-minute calibration.
- It did not solve any of the five decisive instances.
- It did not measure Graviton4 speed.
- It did not read the Springer, SIAM or Sanchez-Flores full texts.
