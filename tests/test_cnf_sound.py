"""Tests for build/cnf_sound (soundness check of direct TT_k-exclusion CNFs) and,
on small cases, for NMH's encoder itself (build/nmh-tour-encode at limit k!).

1. NMH encoder, random partial tournaments (n = 6..10, k = 4..5, <= 13 free
   arcs; in half of the trials the fixed arcs come from a TT_k-free tournament):
   the CNF's models projected to the arcs are exactly the TT_k-free completions
   (brute force over all completions), and cnf_sound says SOUND.
2. Mutations: one literal of one clause flipped or dropped.  For every mutant
   clause cnf_sound's verdict is compared with brute-force soundness (is the
   clause true in every TT_k-free completion?).  cnf_sound may never accept an
   unsound clause; the test also requires that it rejects some.
3. Our encoder (build/encode, direct mode) with --numbering free: SOUND.
4. A wrong header (clause count) is reported.
Run: python3 tests/test_cnf_sound.py   (needs build/cnf_sound, build/nmh-tour-encode, build/encode)
"""
import itertools
import math
import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402

SOUND = ROOT / "build/cnf_sound"
NMH_ENC = ROOT / "build/nmh-tour-encode"
ENC = ROOT / "build/encode"


def nmh_var(a, b):  # 1-based a < b, true iff a -> b
    return a + (b - 2) * (b - 1) // 2


def random_partial(rng, n, nfree, k=None):
    """Random partial tournament; with k, its fixed arcs come from a random TT_k-free tournament
    (so TT_k-free completions exist), else from a uniformly random one."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    while True:
        base = {(i, j): rng.random() < 0.5 for i, j in pairs}
        if k is None:
            break
        out = [0] * n
        for (i, j), c in base.items():
            if c:
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
        if not T.has_tt(out, k):
            break
    free = set(rng.sample(pairs, nfree))
    rows = [["0"] * n for _ in range(n)]
    for i, j in pairs:
        if (i, j) in free:
            rows[i][j] = rows[j][i] = "*"
        else:
            rows[i][j], rows[j][i] = ("1", "0") if base[(i, j)] else ("0", "1")
    return rows, sorted(free)


def completions(rows, free):
    n = len(rows)
    for m in range(1 << len(free)):
        out = [0] * n
        for i in range(n):
            for j in range(i + 1, n):
                c = rows[i][j]
                if c == "*":
                    b = free.index((i, j))
                    c = "1" if (m >> b) & 1 else "0"
                if c == "1":
                    out[i] |= 1 << j
                else:
                    out[j] |= 1 << i
        yield out


def lit_true(out, lit):
    v = abs(lit)
    b = 2
    while (b - 1) * b // 2 < v:
        b += 1
    a = v - (b - 2) * (b - 1) // 2
    ab = (out[a - 1] >> (b - 1)) & 1
    return bool(ab) == (lit > 0)


def read_cnf(path):
    lines = Path(path).read_text().splitlines()
    return lines[0], [[int(x) for x in l.split()][:-1] for l in lines[1:] if l and l[0] not in "pc"]


def write_cnf(path, nv, cls):
    Path(path).write_text(f"p cnf {nv} {len(cls)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in cls))


def checker(mat, k, cnf, numbering="nmh"):
    r = subprocess.run([str(SOUND), str(mat), str(k), str(cnf), "--numbering", numbering, "--quiet"],
                       capture_output=True, text=True)
    return r.returncode == 0 and r.stdout.strip().endswith("SOUND") and "NOT SOUND" not in r.stdout


def main():
    rng = random.Random(46)
    bad = 0
    mut_total = mut_unsound = mut_rejected = n_feasible = 0
    for trial in range(40):
        k = rng.choice([4, 5])
        ttfree_base = trial % 2 == 0
        n = rng.choice([6, 7] if (ttfree_base and k == 4) else [8, 9, 10])   # R(4) = 8
        rows, free = random_partial(rng, n, rng.randint(6, 13), k if ttfree_base else None)
        comps = list(completions(rows, free))
        ttfree = [not T.has_tt(o, k) for o in comps]
        n_feasible += any(ttfree)
        with tempfile.TemporaryDirectory() as td:
            mat = Path(td) / "m.txt"
            T.write_matrix(rows, mat)
            raw = subprocess.run([str(NMH_ENC), str(n), str(k), str(mat), str(math.factorial(k))],
                                 capture_output=True, text=True, check=True).stdout
            body = [[int(x) for x in l.split()][:-1] for l in raw.splitlines()[1:] if l.strip()]
            cnf = Path(td) / "x.cnf"
            write_cnf(cnf, n * (n - 1) // 2, body)
            # 1a. models == TT_k-free completions
            for o, f in zip(comps, ttfree):
                sat = all(any(lit_true(o, l) for l in c) for c in body)
                if sat != f:
                    bad += 1
                    print(f"trial {trial}: NMH CNF disagrees with brute force")
                    break
            # 1b. cnf_sound accepts NMH's CNF
            if not checker(mat, k, cnf):
                bad += 1
                print(f"trial {trial}: cnf_sound rejected NMH's CNF (n={n}, k={k})")
            # 2. mutants of non-unit clauses
            nonunit = [c for c in body if len(c) > 1]
            for _ in range(min(6, len(nonunit))):
                c = list(rng.choice(nonunit))
                i = rng.randrange(len(c))
                if rng.random() < 0.5:
                    c[i] = -c[i]
                else:
                    del c[i]
                sound = all(any(lit_true(o, l) for l in c) for o, f in zip(comps, ttfree) if f)
                one = Path(td) / "one.cnf"
                write_cnf(one, n * (n - 1) // 2, [c])
                acc = checker(mat, k, one)
                mut_total += 1
                mut_unsound += not sound
                mut_rejected += not acc
                if acc and not sound:
                    bad += 1
                    print(f"trial {trial}: cnf_sound ACCEPTED an unsound clause {c}")
            # 3. our encoder, direct mode, free numbering
            ours = Path(td) / "ours.cnf"
            subprocess.run([str(ENC), str(mat), str(k), "5900", str(ours)], check=True, capture_output=True)
            if not checker(mat, k, ours, "free"):
                bad += 1
                print(f"trial {trial}: cnf_sound rejected build/encode's CNF")
            # 4. wrong header
            if trial == 0:
                h, cls = read_cnf(cnf)
                wrong = Path(td) / "wrong.cnf"
                Path(wrong).write_text(f"p cnf {n * (n - 1) // 2} {len(cls) + 1}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in cls))
                if checker(mat, k, wrong):
                    bad += 1
                    print("wrong clause count in the header not reported")
    print(f"trials with a TT_k-free completion: {n_feasible} of 40")
    print(f"mutants: {mut_total}, unsound by brute force: {mut_unsound}, rejected by cnf_sound: {mut_rejected}")
    if mut_unsound == 0 or mut_rejected < mut_unsound:
        bad += 1
        print("mutation test did not exercise rejections")
    print("OK" if bad == 0 else f"FAILED ({bad})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
