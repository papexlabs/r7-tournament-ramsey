# Run 1 (3–5 Nov 2026), archived

Run 1 was the first full AWS run: the TT6-free enumerations n = 21–25 (`enum/`, `stage12.log`, `stage12_check.json`), Stage 3 (`stage3/`, the five `I24X -p- O21*`) and Stage 4 (`stage4/`, NMH's 28 instances), with every UNSAT streamed into `build/lrat-check`.
Its VERIFIED verdicts used the unpatched `lrat-check`, which accepted an empty clause whose hints end without a conflict, so the final empty-clause step of each proof was not checked (every earlier lemma was).
Run 1 therefore does not certify the UNSAT results by itself; run 2, with the patched checker (5 Nov 2026, `notes/FEASIBILITY.md` §14), replaces it.
The files are kept unchanged here (models and cubes stay git-ignored) for comparison with run 2.
