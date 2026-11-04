"""Stage 4: the NMH instances, rebuilt with NMH's own encoder and checked.

The 28 instances (NMH, arXiv 2011.00683, section 5.2):
  ST26-p-TT5                (5.2.1; NMH published no log or input for it)
  ST25-p-H6, ST25-p-W7      (5.2.2; logs in log25/)
  23X-p-Y8, X = A..Y        (5.2.3; logs in log23/)
NMH's "27 hard instances" (their Fig. 6) are the last 27.

CNF = NMH's encoding/tour-encode.c, compiled as in their Makefile, run as
`tour-encode N 7 INPUT 5040` (limit 5040 = 7!: direct clauses only, no 3-cycle
variables), with the placeholder header "p cnf <V> 5000" replaced by the real
clause count; V = 5456 (the encoder's value, as in the log23 headers), except
ST25-p-H6/W7 whose log headers say 496/528 = C(n,2).  This reproduces the
clause count AND the byte count in every one of NMH's 27 logs.

Inputs: NMH's own matrices (log23/*.txt, log25/*.txt) for the 27; for
ST26-p-TT5 our construction data/ST26-p-TT5.txt (ST27 minus vertex 0, pivot,
TT5).  The NMH repo is not redistributed: refs/directed-ramsey-src is fetched
by scripts/fetch_refs.sh (Mac) or by run_stage4.sh (server); every file used is
pinned by sha256 in data/stage4_manifest.json.

Test instances (tests/test_stage4_driver.py only): name "test-<tag>-k<K>",
input data/<name>.txt, TT_K, limit K!.

usage:
  stage4_instances.py st26                    write data/ST26-p-TT5.txt (our input for ST26-p-TT5)
  stage4_instances.py list [--only N1,N2,..]  names (deduplicated), longest expected first
  stage4_instances.py param NAME              "TT_K CUBE_K MAXVAR INPUT" for run_stage4.sh
  stage4_instances.py build NAME...           input -> cnf/stage4/NAME.cnf (kept if its sha256 is
                                              already right); exit 1 unless input, encoder source
                                              and CNF all match the manifest's sha256
  stage4_instances.py verify [NAME...] [--manifest]
        Mac-side checks per instance: input structure (X -> p -> Z, X, Z fixed,
        X x Z free), X and Z isomorphism classes, the 25 X classes distinct,
        clause/byte counts against NMH's log, soundness (build/cnf_sound),
        sha256.  --manifest (re)writes the manifest entries.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402
import instances as I  # noqa: E402

NMH = ROOT / "refs/directed-ramsey-src/Directed-Ramsey-master"
ENC_SRC = NMH / "encoding/tour-encode.c"
ENC_BIN = ROOT / "build/nmh-tour-encode"
SOUND_BIN = ROOT / "build/cnf_sound"
CNF_DIR = ROOT / "cnf/stage4"
MANIFEST = ROOT / "data/stage4_manifest.json"
LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXY"
NAMES = ["ST26-p-TT5", "ST25-p-H6", "ST25-p-W7"] + [f"23{L}-p-Y8" for L in LETTERS]
DEFAULT_CUBE_K = 10


def is_test(name: str) -> bool:
    return name.startswith("test-")


def tt_k(name: str) -> int:
    return int(name.rsplit("-k", 1)[1]) if is_test(name) else 7


def input_path(name: str) -> Path:
    if name == "ST26-p-TT5" or is_test(name):
        return ROOT / f"data/{name}.txt"
    if name.startswith("ST25"):
        return NMH / f"log25/{name}.txt"
    return NMH / f"log23/{name}.txt"


def log_path(name: str) -> Path | None:
    if name == "ST26-p-TT5" or is_test(name):
        return None
    return NMH / (f"log25/{name}.log" if name.startswith("ST25") else f"log23/{name}.log")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for b in iter(lambda: fh.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def header_vars(name: str, n: int) -> int:
    # log23 headers: 5456 = C(32,2) + C(32,3) (the encoder's own value);
    # log25 headers: C(n,2) (496 for n = 32, 528 for n = 33)
    return n * (n - 1) // 2 if name.startswith("ST25") else n * (n - 1) // 2 + n * (n - 1) * (n - 2) // 6


def make_st26_input() -> Path:
    """data/ST26-p-TT5.txt: ST26 = ST27 (data/ST27.txt) minus vertex 0, pivot, TT5 (i -> j for i < j)."""
    st27 = T.matrix_to_out(T.read_matrix(ROOT / "data/ST27.txt"))
    st26 = T.induced(st27, list(range(1, 27)))
    tt5 = [sum(1 << j for j in range(i + 1, 5)) for i in range(5)]
    out = ROOT / "data/ST26-p-TT5.txt"
    T.write_matrix(I.pivot_matrix(st26, tt5), out)
    return out


def ensure_encoder() -> None:
    if not ENC_BIN.exists():
        ENC_BIN.parent.mkdir(exist_ok=True)
        subprocess.run(["gcc", str(ENC_SRC), "-O2", "-o", str(ENC_BIN)], check=True)


def build(name: str, out: Path | None = None) -> Path:
    """NMH encoder -> CNF with the real header.  Returns the CNF path."""
    ensure_encoder()
    src = input_path(name)
    n = len(T.read_matrix(src))
    k = tt_k(name)
    out = out or CNF_DIR / f"{name}.cnf"
    out.parent.mkdir(parents=True, exist_ok=True)
    raw = out.with_suffix(".raw.tmp")
    with open(raw, "wb") as fh:
        subprocess.run([str(ENC_BIN), str(n), str(k), str(src), str(math.factorial(k))], stdout=fh, check=True)
    nlines = 0
    with open(raw, "rb") as fh:
        first = fh.readline()
        assert first.startswith(b"p cnf "), first
        for _ in fh:
            nlines += 1
    tmp = out.with_suffix(".cnf.tmp")
    with open(raw, "rb") as src_fh, open(tmp, "wb") as dst:
        src_fh.readline()
        dst.write(f"p cnf {header_vars(name, n)} {nlines}\n".encode())
        while True:
            b = src_fh.read(1 << 20)
            if not b:
                break
            dst.write(b)
    os.replace(tmp, out)
    raw.unlink()
    return out


def nmh_log_stats(name: str) -> dict | None:
    lp = log_path(name)
    if lp is None:
        return None
    t = lp.read_text(errors="replace")
    g = lambda pat: (m.group(1) if (m := re.search(pat, t, re.M)) else None)  # noqa: E731
    hv, hc = re.search(r"found 'p cnf (\d+) (\d+)' header", t).groups()
    opts = re.findall(r"^c\s+(--\S+)\s+\(different from default", t, re.M)
    return {
        "header_vars": int(hv), "clauses": int(hc), "bytes": int(g(r"after reading (\d+) bytes")),
        "cadical": g(r"^c Version (\S+)"), "options": opts,
        "seconds": float(g(r"total process time since initialization:\s+([\d.]+)")),
        "conflicts": int(g(r"^c conflicts:\s+(\d+)")), "max_rss_mb": float(g(r"maximum resident set size of process:\s+([\d.]+)")),
        "exit": int(g(r"^c exit (\d+)")),
    }


def pivot_parts(rows):
    """(n, arc) for a partial tournament; arc(i, j) is True / False / None (free)."""
    n = len(rows)

    def arc(i, j):  # True if i->j, False if j->i, None if free (upper triangle authoritative)
        c = rows[min(i, j)][max(i, j)]
        return None if c == "*" else ((c == "1") == (i < j))
    return n, arc


def structure(name: str) -> dict:
    """Check the input is a pivot instance X -> p -> Z and identify X and Z up to isomorphism."""
    rows = T.read_matrix(input_path(name))
    n, arc = pivot_parts(rows)
    zname = name.split("-p-")[1]
    b = {"Y8": 8, "H6": 6, "W7": 7, "TT5": 5}[zname]
    a = n - 1 - b
    p = a
    X, Z = list(range(a)), list(range(a + 1, n))
    sx, sz = set(X), set(Z)
    problems = []
    for i in range(n):
        for j in range(i + 1, n):
            c = arc(i, j)
            if (i in sx and j in sz) or (i in sz and j in sx):
                if c is not None:
                    problems.append(f"X x Z pair {i},{j} not free")
            elif c is None:
                problems.append(f"pair {i},{j} free but not in X x Z")
    problems += [f"{x} -> p missing" for x in X if arc(x, p) is not True]
    problems += [f"p -> {z} missing" for z in Z if arc(p, z) is not True]

    def sub(vs):
        out = [0] * len(vs)
        for ii, u in enumerate(vs):
            for jj, v in enumerate(vs):
                if ii != jj and arc(u, v):
                    out[ii] |= 1 << jj
        return out
    xo, zo = sub(X), sub(Z)
    # reference classes from our own data (constructed independently of NMH's inputs)
    if name.startswith("23"):
        xref = T.matrix_to_out(T.read_matrix(ROOT / f"data/I23_{name[2]}.txt"))
    else:  # ST25 / ST26: the unique TT6-free tournament on 25 / 26 vertices, as a subtournament of ST27
        st27 = T.matrix_to_out(T.read_matrix(ROOT / "data/ST27.txt"))
        xref = T.induced(st27, list(range(27 - a, 27)))
    zref = T.matrix_to_out(T.read_matrix(ROOT / f"data/{zname}.txt")) if zname != "TT5" else \
        [sum(1 << j for j in range(i + 1, 5)) for i in range(5)]
    cx, cxr, cz, czr = T.canon_many([xo, xref, zo, zref])
    return {"n": n, "X_size": a, "Z": zname, "free_arcs": a * b, "problems": problems[:10],
            "X_iso_reference": cx == cxr, "Z_iso_reference": cz == czr,
            "X_tt6_free": not T.has_tt(xo, 6), "X_max_tt": T.max_tt(xo), "X_canon": cx}


def verify(name: str) -> dict:
    cnf = CNF_DIR / f"{name}.cnf"
    if not cnf.exists():
        build(name)
    k = tt_k(name)
    n = len(T.read_matrix(input_path(name)))
    rec = {"name": name, "input": str(input_path(name).relative_to(ROOT)), "input_sha256": sha256(input_path(name)),
           "encoder_sha256": sha256(ENC_SRC), "tt_k": k, "limit": math.factorial(k), "maxvar": n * (n - 1) // 2}
    with open(cnf, "rb") as fh:
        h = fh.readline().split()
    rec.update({"vars": int(h[2]), "clauses": int(h[3]), "bytes": cnf.stat().st_size, "cnf_sha256": sha256(cnf)})
    ok = True
    if not is_test(name):
        rec["structure"] = s = structure(name)
        ok = not s["problems"] and s["X_iso_reference"] and s["Z_iso_reference"] and s["X_tt6_free"]
    st = nmh_log_stats(name)
    rec["nmh_log"] = st
    if st:
        rec["matches_nmh_log"] = (st["header_vars"], st["clauses"], st["bytes"]) == (rec["vars"], rec["clauses"], rec["bytes"])
        ok = ok and rec["matches_nmh_log"]
    r = subprocess.run([str(SOUND_BIN), str(input_path(name)), str(k), str(cnf), "--numbering", "nmh", "--quiet"],
                       capture_output=True, text=True)
    rec["soundness"] = r.stdout.strip().splitlines()
    rec["ok"] = ok and r.returncode == 0 and rec["soundness"][-1] == "SOUND"
    return rec


def load_manifest() -> dict:
    return json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {"instances": {}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["list", "param", "build", "verify", "st26"])
    ap.add_argument("names", nargs="*")
    ap.add_argument("--only", default="")
    ap.add_argument("--manifest", action="store_true")
    a = ap.parse_args()
    man = load_manifest()
    inst = man["instances"]
    if a.cmd == "st26":
        print(make_st26_input())
        return
    if a.cmd == "list":
        names = list(dict.fromkeys(a.only.split(","))) if a.only else list(NAMES)
        bad = [x for x in names if x not in NAMES and not is_test(x)]
        if bad:
            sys.exit(f"unknown instance(s): {bad}")
        names.sort(key=lambda x: -inst.get(x, {}).get("expected_vcpu_h", 0))
        print(" ".join(names))
        return
    if a.cmd == "param":
        e = inst[a.names[0]]
        print(e["tt_k"], e.get("cube_k", DEFAULT_CUBE_K), e["maxvar"], e["input"])
        return
    if a.cmd == "build":
        rc = 0
        for name in a.names:
            e = inst.get(name)
            if not e:
                print(f"{name}: no manifest entry"); rc = 1; continue
            if not input_path(name).exists() or sha256(input_path(name)) != e["input_sha256"]:
                print(f"{name}: input missing or sha256 mismatch"); rc = 1; continue
            if sha256(ENC_SRC) != e["encoder_sha256"]:
                print(f"{name}: encoder source sha256 mismatch"); rc = 1; continue
            out = CNF_DIR / f"{name}.cnf"
            if out.exists() and sha256(out) == e["cnf_sha256"]:
                print(f"{name}: CNF already built, sha256 OK"); continue
            out = build(name)
            got = sha256(out)
            if got != e["cnf_sha256"]:
                print(f"{name}: CNF sha256 MISMATCH {got} != {e['cnf_sha256']}"); rc = 1
                out.rename(out.with_suffix(".mismatch"))
            else:
                print(f"{name}: CNF built, sha256 OK {got}")
        sys.exit(rc)
    if a.cmd == "verify":
        rc = 0
        names = a.names or NAMES
        recs = []
        for name in names:
            rec = verify(name)
            recs.append(rec)
            print(json.dumps({k: v for k, v in rec.items() if k not in ("nmh_log",)}), flush=True)
            rc |= not rec["ok"]
        y8 = [r["structure"]["X_canon"] for r in recs if r["name"].endswith("-p-Y8")]
        if len(y8) == 25:
            distinct = len(set(y8)) == 25
            print(f"25 I23 classes pairwise non-isomorphic: {distinct}")
            rc |= not distinct
            man["y8_x_classes_distinct"] = distinct
        if a.manifest:
            for rec in recs:
                old = inst.get(rec["name"], {})
                for key in ("expected_vcpu_h", "cube_k", "projection"):
                    if key in old:
                        rec[key] = old[key]
                inst[rec["name"]] = rec
            order = [x for x in NAMES if x in inst] + sorted(x for x in inst if x not in NAMES)
            man["instances"] = {x: inst[x] for x in order}
            MANIFEST.write_text(json.dumps(man, indent=1) + "\n")
        sys.exit(rc)


if __name__ == "__main__":
    main()
