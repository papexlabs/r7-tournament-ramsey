"""Tests for build/tri_sound (src/tri_sound.c, the independent audit checker of 3-cycle-mode CNFs).

Adapted from the auditor's test_tri.py (5 Nov 2026).  For random partial tournaments (n = 7..9,
k = 4..5, 5..11 free arcs, build/encode ordering limit 1, 3 or 5900, so both 3-cycle clauses and
direct clauses occur):
 1. the CNF that build/encode writes is SOUND;
 2. mutations: one clause that is not a 3-cycle definition loses a literal or has an arc literal
    flipped.  Each mutant clause is compared with brute force (is it true in every TT_k-free
    completion, with every 3-cycle variable set to the cyclic status of its triple?).  tri_sound
    may never accept an unsound mutant, and the test requires that unsound mutants occur;
 3. a wrong header (clause count, or fewer variables than used) is NOT SOUND;
 4. a 3-cycle variable whose definition clauses mention four vertices is NOT SOUND.
Run: python3 tests/test_tri_sound.py   (needs build/tri_sound and build/encode)
"""
import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402

TRI = ROOT / "build/tri_sound"
ENC = ROOT / "build/encode"
rng = random.Random(7)


def parse(p):
    cls, hdr = [], None
    for line in Path(p).read_text().splitlines():
        if line.startswith("p"):
            hdr = line
            continue
        cls.append([int(x) for x in line.split()][:-1])
    return hdr, cls


def write(p, nv, cls, nc=None):
    Path(p).write_text(f"p cnf {nv} {len(cls) if nc is None else nc}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in cls))


def run(m, k, c):
    r = subprocess.run([str(TRI), m, str(k), c], capture_output=True, text=True)
    lines = r.stdout.strip().splitlines()
    return bool(lines) and lines[-1] == "SOUND" and r.returncode == 0


tot = bad_accept = unsound = rejected_good = with_t = 0
extra_bad = extra_n = 0
for trial in range(40):
    n = rng.choice([7, 8, 9])
    k = rng.choice([4, 5])
    nfree = rng.randint(5, 11)
    limit = rng.choice([1, 1, 3, 5900])
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    free = set(rng.sample(pairs, nfree))
    rows = [["0"] * n for _ in range(n)]
    for i, j in pairs:
        c = "*" if (i, j) in free else rng.choice("01")
        rows[i][j] = c
        rows[j][i] = "*" if c == "*" else ("0" if c == "1" else "1")
    with tempfile.TemporaryDirectory() as td:
        m = f"{td}/m.txt"
        T.write_matrix(rows, m)
        c, mp = f"{td}/x.cnf", f"{td}/x.map"
        subprocess.run([str(ENC), m, str(k), str(limit), c, mp], check=True, capture_output=True)
        hdr, cls = parse(c)
        nv = int(hdr.split()[2])
        vmap = {}
        for line in Path(mp).read_text().splitlines():
            f = line.split()
            vmap[int(f[0])] = (f[1], tuple(map(int, f[2:])))
        if not run(m, k, c):
            rejected_good += 1
            print("FAIL encoder CNF rejected", trial, n, k, limit)
        arcv = sorted(v for v, (t, _) in vmap.items() if t == "a")
        tvars = [v for v, (t, _) in vmap.items() if t == "t"]
        with_t += bool(tvars)
        # brute force: every TT_k-free completion, with the 3-cycle variables at their true values
        comps = []
        for mask in range(1 << len(arcv)):
            out = [0] * n
            asg = {}
            for i, j in pairs:
                if rows[i][j] == "1":
                    out[i] |= 1 << j
                elif rows[i][j] == "0":
                    out[j] |= 1 << i
            for b, v in enumerate(arcv):
                i, j = vmap[v][1]
                val = bool(mask >> b & 1)
                asg[v] = val
                if val:
                    out[i] |= 1 << j
                else:
                    out[j] |= 1 << i
            if T.has_tt(out, k):
                continue
            for v in tvars:
                asg[v] = T.three_cycles(T.induced(out, list(vmap[v][1]))) == 1
            comps.append(asg)
        # 2. mutations of clauses that are not 3-cycle definitions (no negative 3-cycle literal)
        cand = [i for i, cl in enumerate(cls) if not any(l < 0 and abs(l) > len(arcv) for l in cl)]
        for _ in range(6):
            if not cand:
                break
            i = rng.choice(cand)
            cl = list(cls[i])
            if not cl:
                continue
            if rng.random() < 0.5 and len(cl) > 1:
                cl.pop(rng.randrange(len(cl)))
            else:
                j = rng.randrange(len(cl))
                if abs(cl[j]) <= len(arcv):
                    cl[j] = -cl[j]
                else:
                    cl.pop(j)
            if not cl:
                continue
            write(c, nv, cls[:i] + [cl] + cls[i + 1:])
            snd = all(any(a[abs(l)] == (l > 0) for l in cl) for a in comps)
            acc = run(m, k, c)
            tot += 1
            unsound += not snd
            if acc and not snd:
                bad_accept += 1
                print("FAIL accepted an unsound clause", trial, cl)
        # 3. wrong headers
        if cls:
            write(c, nv, cls, nc=len(cls) + 1)
            extra_bad += run(m, k, c)
            write(c, max(abs(l) for cl in cls for l in cl) - 1, cls)
            extra_bad += run(m, k, c)
            extra_n += 2
        # 4. a 3-cycle definition clause on a fourth vertex
        defs = [i for i, cl in enumerate(cls) if any(l < 0 and abs(l) > len(arcv) for l in cl)]
        if defs and n >= 4:
            i = defs[0]
            t = next(l for l in cls[i] if l < 0)
            verts = set(vmap[-t][1])
            other = next((v for v, (ty, e) in vmap.items() if ty == "a" and not set(e) <= verts), None)
            if other is not None:
                write(c, nv, cls + [[t, other]])
                extra_bad += run(m, k, c)
                extra_n += 1
print(f"trials 40 (with 3-cycle variables: {with_t}), encoder CNFs rejected {rejected_good}; "
      f"mutants {tot}, unsound {unsound}, unsound accepted {bad_accept}; malformed CNFs accepted {extra_bad} of {extra_n}")
ok = rejected_good == 0 and bad_accept == 0 and unsound > 0 and with_t > 0 and extra_n > 0 and extra_bad == 0
print("ALL OK" if ok else "FAIL")
sys.exit(0 if ok else 1)
