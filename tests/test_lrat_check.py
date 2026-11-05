"""Soundness tests for build/lrat-check (tools/drat-trim/lrat-check.c, patched 5 Nov 2026) and for
the LRAT verdict of scripts/stream_solve.py.

(a) Bogus proofs must NOT verify (all but the last on satisfiable formulas):
    1. empty clause without hints ("3 0 0" on "1 2 0 / -1 2 0": the audit's reproduction);
    2. empty clause whose hints propagate units but end without a conflict;
    3. the same with a RAT hint to a clause those units satisfy (RATs > 0, size 0);
    4. empty clause after valid earlier lemmas, its hints without a conflict;
    5. empty clause with a hint to a clause index that does not exist;
    6. genuine CaDiCaL proofs of UNSAT formulas whose empty-clause line lost its last
       (conflicting) hint, or that end before the empty clause.
(b) Genuine CaDiCaL LRAT proofs (text format, as stream_solve requests them) of small UNSAT
    formulas verify: pigeonhole 5->4 and 6->5, "every tournament on 8 vertices contains TT4"
    (R(4) = 8), and a seeded random 3-SAT formula.
(c) End to end through scripts/stream_solve.py:
    - a fake solver that reads the formula, writes the one-line proof "N 0 0" and exits 20
      (the audit's fake cadical) must not give check VERIFIED (satisfiable and UNSAT formulas);
    - fake checkers: VERIFIED needs exit 0 AND a "c VERIFIED" line AND no "FAILED" / "NOT VERIFIED";
    - the real cadical with the real checker gives VERIFIED on an UNSAT formula (positive control).
Run: python3 tests/test_lrat_check.py
Needs build/lrat-check and cadical (on PATH or $CADICAL).  LRAT_CHECK=path tests another checker
binary instead (the unpatched one fails (a)1-5, (a)6 and the fake-solver runs of (c)).
"""
import itertools
import os
import random
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import stream_solve as S  # noqa: E402

CHECKER = os.environ.get("LRAT_CHECK", str(ROOT / "build/lrat-check"))
CADICAL = os.environ.get("CADICAL", "cadical")
bad = 0


def check(cond, msg):
    global bad
    print(("ok   " if cond else "FAIL ") + msg, flush=True)
    bad += not cond


def write_cnf(path, nv, clauses):
    Path(path).write_text(f"p cnf {nv} {len(clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses))


def run_checker(cnf, proof_text, td, name):
    prf = Path(td) / f"{name}.lrat"
    prf.write_text(proof_text)
    r = subprocess.run([CHECKER, str(cnf), str(prf)], capture_output=True, text=True)
    return S.lrat_verdict(r.returncode, r.stdout + r.stderr), r


def php(p, h):  # p pigeons, h holes: x(i,j) = i*h + j + 1
    x = lambda i, j: i * h + j + 1
    cls = [[x(i, j) for j in range(h)] for i in range(p)]
    cls += [[-x(i, j), -x(k, j)] for j in range(h) for i in range(p) for k in range(i + 1, p)]
    return p * h, cls


def no_ttk(n, k):  # every tournament on n vertices contains TT_k; var(i<j) true iff i -> j
    var, v = {}, 0
    for i in range(n):
        for j in range(i + 1, n):
            v += 1
            var[(i, j)] = v
    arc = lambda u, w: var[(u, w)] if u < w else -var[(w, u)]
    cls = []
    for S_ in itertools.combinations(range(n), k):
        for order in itertools.permutations(S_):
            cls.append([-arc(order[a], order[b]) for a in range(k) for b in range(a + 1, k)])
    return v, cls


def random3(nv, m, seed):
    rng = random.Random(seed)
    return nv, [[v * rng.choice((1, -1)) for v in rng.sample(range(1, nv + 1), 3)] for _ in range(m)]


def lemma_lines(proof_text):
    """(index of the empty-clause line, lines)"""
    lines = proof_text.splitlines()
    for i, line in enumerate(lines):
        f = line.split()
        if len(f) >= 2 and f[1] == "0":
            return i, lines
    return None, lines


def main():
    td = tempfile.mkdtemp(prefix="tlrat_")
    try:
        # (a) bogus proofs
        sat = Path(td) / "sat.cnf"
        write_cnf(sat, 2, [[1, 2], [-1, 2]])
        satu = Path(td) / "satu.cnf"
        write_cnf(satu, 2, [[1], [-1, 2]])
        sat3 = Path(td) / "sat3.cnf"
        write_cnf(sat3, 3, [[1, 2], [-1, 2], [3, -2]])
        cases = [
            ("a1 empty clause, no hints", sat, "3 0 0\n"),
            ("a2 empty clause, unit hints without conflict", satu, "3 0 1 2 0\n"),
            ("a3 empty clause, RAT hint to a satisfied clause", satu, "3 0 1 -1 0\n"),
            ("a4 empty clause after valid lemmas, no conflict", sat3, "4 2 0 1 2 0\n5 3 0 4 3 0\n6 0 4 5 0\n"),
            ("a5 empty clause, hint to a clause that does not exist", satu, "3 0 9000 0\n"),
            ("a5 empty clause, hint far outside the table", satu, "3 0 99999999 0\n"),
        ]
        for name, cnf, proof in cases:
            v, r = run_checker(cnf, proof, td, name.split()[0])
            check(v != "VERIFIED", f"{name}: {v} (exit {r.returncode})")
        # the valid prefix of a4 alone is accepted lemma by lemma (and, lacking an empty clause, not VERIFIED)
        v, r = run_checker(sat3, "4 2 0 1 2 0\n5 3 0 4 3 0\n", td, "a4prefix")
        check("failed while checking" not in r.stdout and v != "VERIFIED",
              "a4 prefix: the earlier lemmas are valid (no lemma fails, no empty clause)")

        # (b) genuine CaDiCaL proofs, and (a)6 their mutilations
        formulas = [("php 5->4", php(5, 4)), ("php 6->5", php(6, 5)), ("no TT4-free 8-tournament", no_ttk(8, 4)),
                    ("random 3-SAT 45 vars ratio 7", random3(45, 315, 3))]
        for name, (nv, cls) in formulas:
            cnf = Path(td) / "f.cnf"
            prf = Path(td) / "f.lrat"
            write_cnf(cnf, nv, cls)
            r = subprocess.run([CADICAL, "-q", "--lrat=true", "--binary=false", str(cnf), str(prf)],
                               capture_output=True, text=True)
            check(r.returncode == 20, f"{name}: cadical says UNSAT (exit {r.returncode})")
            if r.returncode != 20:
                continue
            text = prf.read_text()
            v, rc = run_checker(cnf, text, td, "genuine")
            nlem = sum(1 for line in text.splitlines() if line.split()[1:2] != ["d"])
            check(v == "VERIFIED", f"{name}: genuine proof ({nlem} lemmas) {v}")
            i, lines = lemma_lines(text)
            if i is None:
                check(False, f"{name}: no empty clause in the proof")
                continue
            f = lines[i].split()
            hints = f[2:-1]
            cut = " ".join([f[0], "0"] + hints[:-1] + ["0"])
            v, rc = run_checker(cnf, "\n".join(lines[:i] + [cut]) + "\n", td, "cut")
            check(v != "VERIFIED", f"{name}: empty clause without its last hint ({len(hints)} -> {len(hints) - 1}): {v}")
            v, rc = run_checker(cnf, "\n".join(lines[:i]) + "\n", td, "trunc")
            check(v != "VERIFIED", f"{name}: proof cut before the empty clause: {v}")
            v, rc = run_checker(cnf, "\n".join(lines[:i] + [f"{f[0]} 0 0"]) + "\n", td, "nohint")
            check(v != "VERIFIED", f"{name}: genuine lemmas, then an empty clause without hints: {v}")

        # (c) verdict parsing and end to end through stream_solve
        for rc_, out, want in [(0, "c VERIFIED\n", "VERIFIED"), (1, "c VERIFIED\n", "FAILED"),
                               (0, "c FAILED: x\nc VERIFIED\n", "FAILED"), (0, "c NOT VERIFIED\n", "FAILED"),
                               (0, "", "FAILED"), (0, "c VERIFIED: no\n", "FAILED"), (-6, "c VERIFIED\n", "FAILED")]:
            check(S.lrat_verdict(rc_, out) == want, f"lrat_verdict(exit {rc_}, {out.strip()!r}) = {want}")
        fake = Path(td) / "fake" / "cadical"
        fake.parent.mkdir()
        fake.write_text('#!/bin/bash\n'
                        '# fake solver (audit): reads the whole CNF stream, writes the one-line LRAT proof\n'
                        '# "N 0 0" (empty clause, no hints), exits 20\n'
                        'args=("$@"); prf="${args[$((${#args[@]}-1))]}"; cnf="${args[$((${#args[@]}-2))]}"\n'
                        't=$(mktemp); cat "$cnf" > "$t"; nc=$(head -1 "$t" | awk \'{print $4}\'); rm -f "$t"\n'
                        'echo "$((nc+1)) 0 0" > "$prf"\n'
                        'exit 20\n')
        fake.chmod(0o755)
        body = Path(td) / "body.cnf"
        saved = (S.CADICAL, S.LRAT_CHECK)
        try:
            S.CADICAL, S.LRAT_CHECK = str(fake), CHECKER
            for name, (nv, cls) in [("satisfiable 1 2 / -1 2", (2, [[1, 2], [-1, 2]])), ("UNSAT php 5->4", php(5, 4))]:
                body.write_text("".join(" ".join(map(str, c)) + " 0\n" for c in cls))
                r = S.stream_solve(str(body), nv, len(cls), [], td, "fake")
                check(r["status"] == "UNSAT" and r.get("check") != "VERIFIED",
                      f"stream_solve + fake solver on {name}: status {r['status']}, check {r.get('check')}")
            S.CADICAL = CADICAL
            nv, cls = php(5, 4)
            body.write_text("".join(" ".join(map(str, c)) + " 0\n" for c in cls))
            for out, rc_, want in [("c VERIFIED", 0, "VERIFIED"), ("c VERIFIED", 1, "FAILED"),
                                   ("c FAILED: x\\nc VERIFIED", 0, "FAILED"), ("c NOT VERIFIED", 0, "FAILED"),
                                   ("", 0, "FAILED")]:
                chk = Path(td) / f"chk_{rc_}_{abs(hash(out))}"
                chk.write_text(f'#!/bin/bash\ncat "$1" > /dev/null; cat "$2" > /dev/null\nprintf "{out}\\n"\nexit {rc_}\n')
                chk.chmod(0o755)
                S.LRAT_CHECK = str(chk)
                r = S.stream_solve(str(body), nv, len(cls), [], td, "fakechk")
                check(r["status"] == "UNSAT" and r.get("check") == want,
                      f"stream_solve + fake checker (prints {out!r}, exit {rc_}): check {r.get('check')}, want {want}")
            S.LRAT_CHECK = CHECKER
            r = S.stream_solve(str(body), nv, len(cls), [], td, "real")
            check(r["status"] == "UNSAT" and r.get("check") == "VERIFIED",
                  f"stream_solve + cadical + {Path(CHECKER).name} on php 5->4: {r['status']} {r.get('check')}")
            r = S.stream_solve(str(body), nv, len(cls), ["1 0"], td, "real")
            check(r["status"] == "UNSAT" and r.get("check") == "VERIFIED",
                  f"... with a cube unit: {r['status']} {r.get('check')}")
        finally:
            S.CADICAL, S.LRAT_CHECK = saved
    finally:
        shutil.rmtree(td, ignore_errors=True)
    print("ALL OK" if bad == 0 else f"FAILED ({bad})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
