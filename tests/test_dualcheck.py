"""Tests for the second proof check: scripts/audit/dualcheck.sh (patched lrat-check and the formally
verified cake_lpr side by side) and scripts/audit/cake_sample.py.

(a) Verdict rules: cake_lpr is VERIFIED only on exit 0 with stdout exactly "s VERIFIED UNSAT" and an
    empty stderr; dualcheck says "c VERIFIED" (exit 0) only if both checkers do (fake checkers).
(b) Genuine CaDiCaL LRAT proofs verify (pigeonhole 5->4 and 6->5, every 8-tournament has a TT4,
    random 3-SAT), from files and from named pipes, and both checkers say VERIFIED in the log.
(c) Bogus proofs fail, and each checker rejects them on its own (DUALCHECK_KEEP_GOING=1): an empty
    clause without a conflict on a satisfiable formula (no hints, unit hints, a RAT hint), genuine
    proofs cut before the empty clause or with the empty clause's last hint removed, garbage text,
    random bytes, an empty proof.
(d) A checker that exits early (without reading, after the formula, or in the middle of the
    proof) gives NOT VERIFIED and no hang, with large inputs written into named pipes by writer
    threads as in stream_solve (the writers must finish too).
(e) stream_solve with LRAT_CHECK = dualcheck.sh: VERIFIED on an UNSAT formula (also with a cube
    unit); not VERIFIED on a satisfiable one; a fake solver that writes "N 0 0" and exits 20 is
    not VERIFIED.
(f) cake_sample.py end to end: cubes mode on a small cube-and-conquer run made here
    (make_cubes.py + run_cubes.py), enum mode on the k = 5, n = 10 enumeration (certify_first.py,
    pivot_enum.py, certify_enum.py); negative cases: a body.cnf that does not match body.sha256 is
    refused, a "leaf" that is satisfiable is NOT VERIFIED, a job with a dropped model (its formula
    becomes satisfiable) is NOT VERIFIED and a model that does not fit its job is MODEL_MISMATCH.
Run: python3 tests/test_dualcheck.py   (needs build/lrat-check, build/cake_lpr, build/pivenum, cadical)
"""
import itertools
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "audit"))
import stream_solve as S  # noqa: E402
from dualcheck import cake_verdict  # noqa: E402

DUAL = str(ROOT / "scripts/audit/dualcheck.sh")
CADICAL = os.environ.get("CADICAL", "cadical")
PY = sys.executable
bad = 0


def check(cond, msg):
    global bad
    print(("ok   " if cond else "FAIL ") + msg, flush=True)
    bad += not cond


def write_cnf(path, nv, clauses):
    Path(path).write_text(f"p cnf {nv} {len(clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses))


def php(p, h):
    x = lambda i, j: i * h + j + 1
    cls = [[x(i, j) for j in range(h)] for i in range(p)]
    cls += [[-x(i, j), -x(k, j)] for j in range(h) for i in range(p) for k in range(i + 1, p)]
    return p * h, cls


def no_ttk(n, k):
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


def dual(cnf, proof, env=None, timeout=120):
    e = dict(os.environ)
    e.update(env or {})
    r = subprocess.run([DUAL, str(cnf), str(proof)], capture_output=True, text=True, env=e, timeout=timeout)
    return r


def last_log(logdir):
    logs = sorted(Path(logdir).glob("*.json"), key=lambda p: p.stat().st_mtime)
    return json.loads(logs[-1].read_text()) if logs else {}


def verified(r):
    return r.returncode == 0 and r.stdout.splitlines()[-1:] == ["c VERIFIED"]


def not_verified(r):
    return r.returncode == 1 and r.stdout.splitlines()[-1:] == ["c NOT VERIFIED"]


def fake(td, name, body):
    p = Path(td) / name
    p.write_text("#!/bin/bash\n" + body + "\n")
    p.chmod(0o755)
    return str(p)


def through_fifos(td, cnf_bytes, proof_bytes, env, timeout=120):
    """dualcheck on two named pipes written by threads (as stream_solve does); (result, writers done)"""
    d = Path(tempfile.mkdtemp(dir=td))
    fc, fp = d / "c.fifo", d / "p.fifo"
    os.mkfifo(fc)
    os.mkfifo(fp)
    state = {}

    def writer(path, data, key):
        try:
            with open(path, "wb") as fh:
                for i in range(0, len(data), 1 << 16):
                    fh.write(data[i:i + (1 << 16)])
            state[key] = "all written"
        except BrokenPipeError:
            state[key] = "broken pipe"

    ws = [threading.Thread(target=writer, args=(fc, cnf_bytes, "cnf"), daemon=True),
          threading.Thread(target=writer, args=(fp, proof_bytes, "proof"), daemon=True)]
    for w in ws:
        w.start()
    t0 = time.time()
    try:
        r = dual(fc, fp, env, timeout)
    except subprocess.TimeoutExpired:
        r = None
    for w in ws:
        w.join(timeout=30)
    return r, all(not w.is_alive() for w in ws), round(time.time() - t0, 1), state


def cadical_proof(td, name, nv, cls):
    cnf, prf = Path(td) / f"{name}.cnf", Path(td) / f"{name}.lrat"
    write_cnf(cnf, nv, cls)
    r = subprocess.run([CADICAL, "-q", "--lrat=true", "--binary=false", str(cnf), str(prf)],
                       capture_output=True, text=True)
    return cnf, prf, r.returncode


def main():
    td = tempfile.mkdtemp(prefix="tdual_")
    logdir = Path(td) / "logs"
    env = {"DUALCHECK_LOG_DIR": str(logdir)}
    try:
        # (a) verdict rules
        for args, want in [((0, "s VERIFIED UNSAT\n", ""), "VERIFIED"), ((1, "s VERIFIED UNSAT\n", ""), "FAILED"),
                           ((0, "s VERIFIED UNSAT\n", "c Checking failed at line: 3\n"), "FAILED"),
                           ((0, "c note\ns VERIFIED UNSAT\n", ""), "FAILED"), ((0, "s VERIFIED UNSAT \n", ""), "FAILED"),
                           ((0, "", "c empty clause not derived at end of proof\n"), "FAILED"),
                           ((3, "", "CakeML heap space exhausted.\n"), "FAILED"), ((-9, "s VERIFIED UNSAT\n", ""), "FAILED")]:
            check(cake_verdict(*args) == want, f"cake_verdict{args!r} = {want}")
        nv, cls = php(5, 4)
        cnf, prf, rc = cadical_proof(td, "php54", nv, cls)
        check(rc == 20, "cadical: php 5->4 UNSAT")
        good_lrat = fake(td, "lrat_ok", 'cat "$1" > /dev/null; cat "$2" > /dev/null; echo "c VERIFIED"')
        good_cake = fake(td, "cake_ok", 'cat "$1" > /dev/null; cat "$2" > /dev/null; echo "s VERIFIED UNSAT"')
        for name, e, want in [
            ("both fakes verify", {"DUALCHECK_LRAT": good_lrat, "DUALCHECK_CAKE": good_cake}, True),
            ("cake prints an extra line", {"DUALCHECK_CAKE": fake(td, "c1", 'cat "$1" "$2" > /dev/null; echo c x; echo "s VERIFIED UNSAT"')}, False),
            ("cake verified but exit 1", {"DUALCHECK_CAKE": fake(td, "c2", 'cat "$1" "$2" > /dev/null; echo "s VERIFIED UNSAT"; exit 1')}, False),
            ("cake verified but writes stderr", {"DUALCHECK_CAKE": fake(td, "c3", 'cat "$1" "$2" > /dev/null; echo "s VERIFIED UNSAT"; echo oops >&2')}, False),
            ("lrat-check exit 0 without 'c VERIFIED'", {"DUALCHECK_LRAT": fake(td, "l1", 'cat "$1" "$2" > /dev/null; echo "c verified"')}, False),
            ("lrat-check 'c VERIFIED' but exit 1", {"DUALCHECK_LRAT": fake(td, "l2", 'cat "$1" "$2" > /dev/null; echo "c VERIFIED"; exit 1')}, False),
            ("lrat-check 'c VERIFIED' and 'FAILED'", {"DUALCHECK_LRAT": fake(td, "l3", 'cat "$1" "$2" > /dev/null; echo "c FAILED: x"; echo "c VERIFIED"')}, False),
            ("missing cake_lpr binary", {"DUALCHECK_CAKE": str(Path(td) / "no_such_binary")}, False),
        ]:
            r = dual(cnf, prf, {**env, **e})
            check(verified(r) if want else not_verified(r),
                  f"fake checkers, {name}: exit {r.returncode}, {r.stdout.strip().splitlines()[-1:]}")

        # (b) genuine proofs
        for name, (nv, cls) in [("php 5->4", php(5, 4)), ("php 6->5", php(6, 5)), ("no TT4-free 8-tournament", no_ttk(8, 4)),
                                ("random 3-SAT 45 vars ratio 7", random3(45, 315, 3))]:
            cnf, prf, rc = cadical_proof(td, "g", nv, cls)
            if rc != 20:
                check(False, f"{name}: cadical exit {rc}")
                continue
            r = dual(cnf, prf, env)
            lg = last_log(logdir)
            check(verified(r) and lg["lrat"]["verdict"] == "VERIFIED" and lg["cake"]["verdict"] == "VERIFIED",
                  f"{name}: genuine proof from files: {r.stdout.strip().splitlines()[-1:]} "
                  f"(log: lrat-check {lg['lrat']['verdict']}, cake_lpr {lg['cake']['verdict']})")
            r, done, secs, _ = through_fifos(td, cnf.read_bytes(), prf.read_bytes(), env)
            check(r is not None and verified(r) and done, f"{name}: genuine proof through named pipes, {secs}s")
            genuine = (cnf, prf.read_text())

        # (c) bogus proofs: each checker must reject on its own
        sat = Path(td) / "sat.cnf"
        write_cnf(sat, 2, [[1, 2], [-1, 2]])
        satu = Path(td) / "satu.cnf"
        write_cnf(satu, 2, [[1], [-1, 2]])
        cnf, text = genuine
        lines = text.splitlines()
        i = next(i for i, l in enumerate(lines) if l.split()[1:2] == ["0"])
        f = lines[i].split()
        cases = [("empty clause, no hints (satisfiable)", sat, "3 0 0\n"),
                 ("empty clause, unit hints without conflict (satisfiable)", satu, "3 0 1 2 0\n"),
                 ("empty clause, RAT hint (satisfiable)", satu, "3 0 1 -1 0\n"),
                 ("genuine proof cut before the empty clause", cnf, "\n".join(lines[:i]) + "\n"),
                 ("genuine proof, empty clause without its last hint", cnf,
                  "\n".join(lines[:i] + [" ".join([f[0], "0"] + f[2:-2] + ["0"])]) + "\n"),
                 ("genuine lemmas, then an empty clause without hints", cnf, "\n".join(lines[:i] + [f"{f[0]} 0 0"]) + "\n"),
                 ("garbage text", cnf, "hello world\n"),
                 ("empty proof", cnf, "")]
        for name, formula, proof in cases + [("random bytes", cnf, None)]:
            p = Path(td) / "bogus.lrat"
            if proof is None:
                p.write_bytes(bytes(random.Random(5).randrange(256) for _ in range(4000)))
            else:
                p.write_text(proof)
            r = dual(formula, p, {**env, "DUALCHECK_KEEP_GOING": "1"})
            lg = last_log(logdir)
            both = lg.get("lrat", {}).get("verdict") == "FAILED" and lg.get("cake", {}).get("verdict") == "FAILED"
            check(not_verified(r) and both, f"{name}: NOT VERIFIED, both reject: lrat-check '{lg['lrat']['said']}', "
                                            f"cake_lpr '{lg['cake']['said']}'")
        r = dual(sat, Path(td) / "bogus.lrat", env)        # random bytes again, fail fast (default)
        check(not_verified(r), f"fail fast: {r.stdout.strip().splitlines()[:2]}")

        # (d) early exit: large inputs through named pipes; nothing may hang
        big_nv, big_cls = random3(3000, 120000, 11)               # ~1.7 MB formula, larger than any pipe buffer
        big_cnf = (f"p cnf {big_nv} {len(big_cls)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in big_cls)).encode()
        big_prf = b"".join(f"{len(big_cls) + 1 + j} {j % 3000 + 1} 0 1 2 3 0\n".encode() for j in range(400000))  # ~10 MB
        quick = fake(td, "exit_now", 'echo "gone"; exit 0')
        cnf_only = fake(td, "cnf_then_exit", 'cat "$1" > /dev/null; head -c 1000 "$2" > /dev/null; echo "s VERIFIED UNSAT"')
        lies = fake(td, "lies", 'echo "s VERIFIED UNSAT"')
        for name, e in [("cake_lpr exits at once", {"DUALCHECK_CAKE": quick}),
                        ("lrat-check exits at once", {"DUALCHECK_LRAT": quick}),
                        ("cake_lpr reads the formula and 1000 proof bytes, then exits",
                         {"DUALCHECK_CAKE": cnf_only}),
                        ("cake_lpr says VERIFIED without reading (lrat-check must decide)", {"DUALCHECK_CAKE": lies}),
                        ("lrat-check exits at once, the other runs to the end (KEEP_GOING)",
                         {"DUALCHECK_LRAT": quick, "DUALCHECK_KEEP_GOING": "1"}),
                        ("both exit at once", {"DUALCHECK_LRAT": quick, "DUALCHECK_CAKE": quick})]:
            r, done, secs, st = through_fifos(td, big_cnf, big_prf, {**env, **e}, timeout=180)
            check(r is not None and not_verified(r) and done,
                  f"{name}: {'NOT VERIFIED' if r is not None and not_verified(r) else r and r.stdout}, "
                  f"no hang ({secs}s), writers {st}")

        # (e) stream_solve with LRAT_CHECK = dualcheck.sh
        saved = (S.CADICAL, S.LRAT_CHECK)
        os.environ["DUALCHECK_LOG_DIR"] = str(logdir)
        try:
            S.LRAT_CHECK = DUAL
            body = Path(td) / "body.cnf"
            nv, cls = php(5, 4)
            body.write_text("".join(" ".join(map(str, c)) + " 0\n" for c in cls))
            r = S.stream_solve(str(body), nv, len(cls), [], td, "dual")
            lg = last_log(logdir)
            check(r["status"] == "UNSAT" and r.get("check") == "VERIFIED" and lg["cake"]["verdict"] == "VERIFIED",
                  f"stream_solve + cadical + dualcheck on php 5->4: {r['status']} {r.get('check')}, "
                  f"cake_lpr {lg['cake']['verdict']}")
            r = S.stream_solve(str(body), nv, len(cls), ["1 0"], td, "dual")
            check(r["status"] == "UNSAT" and r.get("check") == "VERIFIED", f"... with a cube unit: {r['status']} {r.get('check')}")
            nv9, cls9 = php(9, 8)                      # a 7 MB proof: more than the pipe buffers hold
            body.write_text("".join(" ".join(map(str, c)) + " 0\n" for c in cls9))
            r = S.stream_solve(str(body), nv9, len(cls9), [], td, "dual")
            check(r["status"] == "UNSAT" and r.get("check") == "VERIFIED", f"stream_solve + dualcheck on php 9->8: "
                                                                          f"{r['status']} {r.get('check')}")
            for name, var in [("cake_lpr", "DUALCHECK_CAKE"), ("lrat-check", "DUALCHECK_LRAT")]:
                os.environ[var] = quick
                res = {}
                th = threading.Thread(target=lambda: res.update(S.stream_solve(str(body), nv9, len(cls9), [], td, "early")),
                                      daemon=True)
                t0 = time.time()
                th.start()
                th.join(timeout=120)
                os.environ.pop(var)
                check(not th.is_alive() and res.get("check") != "VERIFIED",
                      f"stream_solve on php 9->8, {name} exits at once: returns ({round(time.time() - t0, 1)}s), "
                      f"status {res.get('status')}, check {res.get('check')}")
            nv2, cls2 = random3(40, 120, 1)
            body.write_text("".join(" ".join(map(str, c)) + " 0\n" for c in cls2))
            r = S.stream_solve(str(body), nv2, len(cls2), [], td, "dual")
            check(r["status"] == "SAT" and r.get("check") != "VERIFIED",
                  f"stream_solve + dualcheck on a satisfiable formula: {r['status']} check {r.get('check')}")
            fk = fake(td, "cadical_fake",
                      '# fake solver: reads the CNF, writes the proof "N 0 0", exits 20\n'
                      'args=("$@"); prf="${args[$((${#args[@]}-1))]}"; cnf="${args[$((${#args[@]}-2))]}"\n'
                      't=$(mktemp); cat "$cnf" > "$t"; nc=$(head -1 "$t" | awk \'{print $4}\'); rm -f "$t"\n'
                      'echo "$((nc+1)) 0 0" > "$prf"\nexit 20')
            S.CADICAL = fk
            for name, (nv_, cls_) in [("satisfiable", (2, [[1, 2], [-1, 2]])), ("UNSAT php 5->4", php(5, 4))]:
                body.write_text("".join(" ".join(map(str, c)) + " 0\n" for c in cls_))
                r = S.stream_solve(str(body), nv_, len(cls_), [], td, "dualfake")
                lg = last_log(logdir)
                check(r["status"] == "UNSAT" and r.get("check") != "VERIFIED",
                      f"stream_solve + fake solver 'N 0 0' on {name}: check {r.get('check')} "
                      f"(cake_lpr: {lg['cake']['said']})")
        finally:
            S.CADICAL, S.LRAT_CHECK = saved
            os.environ.pop("DUALCHECK_LOG_DIR", None)

        # (f) cake_sample.py end to end
        sample = [PY, "-I", str(ROOT / "scripts/audit/cake_sample.py")]
        nv, cls = no_ttk(8, 4)
        full = Path(td) / "tt.cnf"
        write_cnf(full, nv, cls)
        icnf = Path(td) / "tt.icnf"
        subprocess.run([PY, "-I", str(ROOT / "scripts/make_cubes.py"), str(full), str(icnf), "--k", "3"],
                       check=True, capture_output=True)
        run = Path(td) / "ttrun" / "run"
        subprocess.run([PY, "-I", str(ROOT / "scripts/run_cubes.py"), str(full), str(icnf), str(run), "--workers", "2",
                        "--timeouts", "0", "--min-free-gb", "0"], check=True, capture_output=True)
        out = Path(td) / "cs_cubes"
        r = subprocess.run(sample + ["cubes", str(run), "--out", str(out), "--n", "5", "--slowest", "2", "--workers", "2",
                                     "--heap", "256"], capture_output=True, text=True, timeout=300)
        s = json.loads((out / "summary.json").read_text()) if (out / "summary.json").exists() else {}
        check(r.returncode == 0 and s.get("ALL VERIFIED BY BOTH") is True and s.get("sha_check") == "OK"
              and s.get("sampled", 0) >= 5, f"cake_sample cubes on an 8-cube run: {s.get('verified_by_both')}/"
                                         f"{s.get('sampled')} verified by both, sha {s.get('sha_check')}")
        r = subprocess.run(sample + ["cubes", str(run), "--out", str(out), "--n", "5", "--slowest", "2"],
                           capture_output=True, text=True, timeout=300)
        check(r.returncode == 0 and "to do: 0" in r.stdout, "cake_sample cubes resumes (nothing to do)")
        leaf_ids = sorted(json.loads(l)["id"] for l in (run / "results.jsonl").read_text().splitlines()
                          if json.loads(l)["status"] == "UNSAT")[:3]
        cids = Path(td) / "cube_ids.json"
        cids.write_text(json.dumps(leaf_ids))
        out = Path(td) / "cs_cubes_ids"
        r = subprocess.run(sample + ["cubes", str(run), "--out", str(out), "--n", "0", "--slowest", "0", "--ids",
                                     str(cids), "--workers", "2", "--heap", "256"],
                           capture_output=True, text=True, timeout=300)
        s = json.loads((out / "summary.json").read_text()) if (out / "summary.json").exists() else {}
        check(r.returncode == 0 and s.get("ALL VERIFIED BY BOTH") is True and s.get("sampled") == len(leaf_ids) == 3,
              f"cake_sample cubes --n 0 --slowest 0 --ids (3 listed leaves): {s.get('verified_by_both')}/{s.get('sampled')}")
        cids.write_text(json.dumps(leaf_ids + ["999.9"]))
        r = subprocess.run(sample + ["cubes", str(run), "--out", str(Path(td) / "cs_cubes_ids_bad"), "--n", "0",
                                     "--slowest", "0", "--ids", str(cids)], capture_output=True, text=True, timeout=300)
        check(r.returncode != 0 and "--ids" in r.stderr, "cake_sample cubes refuses an --ids id that is not an UNSAT leaf")
        bad_run = Path(td) / "badrun" / "run"
        shutil.copytree(run, bad_run, ignore=shutil.ignore_patterns("tmp"))
        with open(bad_run / "body.cnf", "a") as fh:
            fh.write("1 2 0\n")
        r = subprocess.run(sample + ["cubes", str(bad_run), "--out", str(Path(td) / "cs_bad")],
                           capture_output=True, text=True, timeout=300)
        check(r.returncode != 0 and "MISMATCH" in r.stderr, f"cake_sample refuses a body.cnf with the wrong sha256: "
                                                            f"{r.stderr.strip()[-90:]}")
        sat_run = Path(td) / "satrun" / "run"
        sat_run.mkdir(parents=True)
        nv2, cls2 = random3(40, 120, 1)
        (sat_run / "body.cnf").write_text("".join(" ".join(map(str, c)) + " 0\n" for c in cls2))
        (sat_run / "body.meta").write_text(f"{nv2} {len(cls2)}\n")
        (sat_run / "results.jsonl").write_text(json.dumps({"id": "0", "lits": [1], "level": 0, "status": "UNSAT",
                                                           "check": "VERIFIED", "secs": 1.0}) + "\n")
        r = subprocess.run(sample + ["cubes", str(sat_run), "--out", str(Path(td) / "cs_sat"), "--n", "1"],
                           capture_output=True, text=True, timeout=300)
        s = json.loads((Path(td) / "cs_sat" / "summary.json").read_text())
        check(r.returncode == 1 and s["ALL VERIFIED BY BOTH"] is False and s["verified_by_both"] == 0,
              f"cake_sample cubes on a satisfiable 'leaf': NOT VERIFIED ({s['not_verified'][:1]})")

        en = Path(td) / "k5n10"
        for cmd in (["certify_first.py", "5", "10", str(en), "--workers", "2"], ["pivot_enum.py", "5", "10", str(en)],
                    ["certify_enum.py", str(en), "--workers", "2"]):
            subprocess.run([PY, "-I", str(ROOT / "scripts" / cmd[0])] + cmd[1:], check=True, capture_output=True)
        out = Path(td) / "cs_enum"
        r = subprocess.run(sample + ["enum", str(en), "--out", str(out), "--n", "100", "--workers", "3"],
                           capture_output=True, text=True, timeout=300)
        s = json.loads((out / "summary.json").read_text()) if (out / "summary.json").exists() else {}
        check(r.returncode == 0 and s.get("ALL VERIFIED BY BOTH") is True and s.get("sampled") == s.get("jobs") == 12,
              f"cake_sample enum k=5 n=10: {s.get('verified_by_both')}/{s.get('sampled')} jobs verified by both "
              f"({s.get('jobs_with_models')} with models)")
        ids = Path(td) / "ids.json"
        recs10 = [json.loads(l) for l in (en / "records.jsonl").read_text().splitlines()]
        two = sorted([r_["d"], r_["ia"], r_["ib"]] for r_ in recs10)[:2]
        ids.write_text(json.dumps(two))
        out = Path(td) / "cs_enum_ids"
        r = subprocess.run(sample + ["enum", str(en), "--out", str(out), "--n", "0", "--ids", str(ids), "--workers", "2"],
                           capture_output=True, text=True, timeout=300)
        s = json.loads((out / "summary.json").read_text()) if (out / "summary.json").exists() else {}
        check(r.returncode == 0 and s.get("ALL VERIFIED BY BOTH") is True and s.get("sampled") == 2,
              f"cake_sample enum --n 0 --ids (2 listed jobs): {s.get('verified_by_both')}/{s.get('sampled')}")
        ids.write_text(json.dumps(two + [[99, 0, 0]]))
        r = subprocess.run(sample + ["enum", str(en), "--out", str(Path(td) / "cs_enum_ids_bad"), "--n", "0", "--ids",
                                     str(ids), "--workers", "2"], capture_output=True, text=True, timeout=300)
        check(r.returncode != 0 and "--ids" in r.stderr, "cake_sample enum refuses an --ids job that is not a job")
        neg = Path(td) / "k5n10neg"
        shutil.copytree(en, neg)
        recs = [json.loads(l) for l in (neg / "records.jsonl").read_text().splitlines()]
        victims = [r_ for r_ in recs if r_["models"] > 1][:2]
        drop_key = (victims[0]["d"], victims[0]["ia"], victims[0]["ib"])
        flip_key = (victims[1]["d"], victims[1]["ia"], victims[1]["ib"])
        dropped = flipped = False
        for p in sorted((neg / "models").glob("*.d6")):
            keep = []
            for l in p.read_text().splitlines():
                fl = l.split()
                key = (int(fl[0]), int(fl[1]), int(fl[2]))
                if key == drop_key and not dropped:
                    dropped = True
                    continue
                keep.append(l)
            p.write_text("\n".join(keep) + ("\n" if keep else ""))
        for r_ in recs:                        # the record must agree with the files: one model fewer
            if (r_["d"], r_["ia"], r_["ib"]) == drop_key:
                r_["models"] -= 1
        (neg / "records.jsonl").write_text("".join(json.dumps(r_) + "\n" for r_ in recs))
        sys.path.insert(0, str(ROOT / "src"))
        import tourn as Tn
        for p in sorted((neg / "models").glob("*.d6")):
            ls = p.read_text().splitlines()
            for j, l in enumerate(ls):
                fl = l.split()
                if (int(fl[0]), int(fl[1]), int(fl[2])) == flip_key and not flipped:
                    o = Tn.from_d6(fl[3])
                    o[0] ^= 1 << 1                 # reverse the arc between vertices 0 and 1 (inside A)
                    o[1] ^= 1 << 0
                    ls[j] = " ".join(fl[:3] + [Tn.to_d6(o)])
                    flipped = True
            p.write_text("\n".join(ls) + "\n")
        out = Path(td) / "cs_enum_neg"
        r = subprocess.run(sample + ["enum", str(neg), "--out", str(out), "--n", "100", "--workers", "3"],
                           capture_output=True, text=True, timeout=300)
        got = {json.loads(l)["id"]: json.loads(l) for l in (out / "items.jsonl").read_text().splitlines()}
        dk, fk_ = "_".join(map(str, drop_key)), "_".join(map(str, flip_key))
        check(dropped and r.returncode == 1 and got[dk]["status"] == "SAT" and got[dk]["verdict"] == "NOT VERIFIED",
              f"cake_sample enum, job {dk} with a dropped model: {got[dk]['status']} {got[dk]['verdict']}")
        check(flipped and got[fk_]["status"] == "MODEL_MISMATCH" and got[fk_]["verdict"] == "NOT VERIFIED",
              f"cake_sample enum, job {fk_} with a model that does not fit: {got[fk_]['status']} "
              f"({got[fk_].get('problem')})")
        others = [v for k_, v in got.items() if k_ not in (dk, fk_)]
        check(all(v["verdict"] == "VERIFIED" for v in others), f"cake_sample enum, the other {len(others)} jobs VERIFIED")
    finally:
        shutil.rmtree(td, ignore_errors=True)
    print("ALL OK" if bad == 0 else f"FAILED ({bad})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
