"""End-to-end test of scripts/cloud/run_stage4.sh on two small NMH-encoded instances (TT_5, k = 5),
run in a temporary copy of the repository (the real results/ is never touched).

  test-u-k5: TT4-free 6-vertex -p- TT4-free 7-vertex (14 vertices, so UNSAT since R(5) = 14)
  test-v-k5: the reversed 6-vertex part -p- the same 7-vertex one
  test-e-k5: TT5-free 6 -p- TT5-free 7 whose fixed arcs already contain TT5 (failed-check path)
  test-s-k5: N-(v) -p- N+(v) of the 13-vertex TT5-free tournament (SAT: the tournament itself)

Checks:
 1. the manifest step (stage4_instances.py verify --manifest) accepts both instances (soundness SOUND);
 2. stage on test-u: DONE = 0 and cnc_summary ALL CLOSED;
 3. rerun of the same stage resumes: no new cube records, still DONE = 0; a stage with two
    instances and one slot runs the open one and skips the closed one;
 3b. a failed LRAT check is logged and the stage ends NOT CLOSED with DONE = 1;
 3c. without SLOTS / TIMEOUTS the driver runs all instances side by side with the timeouts
     1800,3600,1800,7200,0 (the defaults since 5 Nov 2026);
 4. stage on test-s + test-u: the SAT cube is found, verify_model.py confirms a TT5-free model,
    results/STAGE.SAT is written and DONE = 1; a rerun refuses to start;
 5. a CNF whose sha256 differs from the manifest is refused (PREPARE FAILED, DONE = 1);
 6. verify_model.py --model rejects a corrupted model.
Run: python3 tests/test_stage4_driver.py   (needs gcc, build/lrat-check,
build/cnf_sound, cadical on PATH and refs/directed-ramsey-src from scripts/fetch_refs.sh)
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402
import instances as I  # noqa: E402

bad = 0


def check(cond, msg):
    global bad
    print(("ok   " if cond else "FAIL ") + msg)
    bad += not cond


def run(cmd, cwd, env=None):
    return subprocess.run(cmd, cwd=cwd, env=dict(os.environ, **(env or {})), capture_output=True, text=True)


def main():
    with tempfile.TemporaryDirectory() as td:
        r = Path(td)
        shutil.copytree(ROOT / "scripts", r / "scripts", ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(ROOT / "src", r / "src", ignore=shutil.ignore_patterns("__pycache__"))
        (r / "build").mkdir()
        for b in ("lrat-check", "cnf_sound"):     # nmh-tour-encode is compiled by the driver itself
            shutil.copy2(ROOT / "build" / b, r / "build" / b)
        (r / "refs").mkdir()
        os.symlink(ROOT / "refs/directed-ramsey-src", r / "refs/directed-ramsey-src")
        (r / "data").mkdir()
        # instances
        # X and Z TT4-free, so that no TT5 lies in the fixed arcs (X + p, p + Z): the CNF has no empty clause
        tt6 = T.from_d6((ROOT / "data/tt4free/tt4free6.d6").read_text().split()[0])
        tt7 = T.from_d6((ROOT / "data/tt4free/tt4free7.d6").read_text().split()[0])
        T.write_matrix(I.pivot_matrix(tt6, tt7), r / "data/test-u-k5.txt")
        # test-e: TT5-free (not TT4-free) parts, so the fixed arcs contain TT5s, the CNF has empty
        # clauses, and lrat-check reports these trivial UNSATs as not verified (a failed check)
        t5a = T.from_d6((ROOT / "data/tt5free/tt5free6.d6").read_text().split()[0])
        t5b = T.from_d6((ROOT / "data/tt5free/tt5free7.d6").read_text().split()[0])
        T.write_matrix(I.pivot_matrix(t5a, t5b), r / "data/test-e-k5.txt")
        tt6b = T.reverse(tt6)
        T.write_matrix(I.pivot_matrix(tt6b, tt7), r / "data/test-v-k5.txt")
        st13 = T.from_d6((ROOT / "data/tt5free/tt5free13.d6").read_text().split()[0])
        v = 0
        nin = [u for u in range(13) if (st13[u] >> v) & 1]
        nout = [u for u in range(13) if (st13[v] >> u) & 1]
        T.write_matrix(I.pivot_matrix(T.induced(st13, nin), T.induced(st13, nout)), r / "data/test-s-k5.txt")
        p = run([sys.executable, "scripts/stage4_instances.py", "verify", "test-u-k5", "test-v-k5", "test-s-k5", "test-e-k5", "--manifest"], r)
        (r / "build/nmh-tour-encode").unlink()   # the driver must compile it (once, before the parallel builds)
        check(p.returncode == 0, f"manifest step accepts the test instances ({p.stdout.strip()[-120:]})")
        man = json.loads((r / "data/stage4_manifest.json").read_text())
        for e in man["instances"].values():
            e["cube_k"] = 3
        (r / "data/stage4_manifest.json").write_text(json.dumps(man))
        for f in (r / "cnf/stage4").glob("*.cnf"):
            f.unlink()          # the driver must rebuild them and match the manifest
        env = {"SLOTS": "2", "POLL": "1", "TIMEOUTS": "30,30,0"}
        drv = ["bash", "scripts/cloud/run_stage4.sh"]

        # 2. UNSAT instance closes
        p = run(drv + ["stage4-tu", "2", "1"], r, dict(env, STAGE4_NAMES="test-u-k5"))
        done = (r / "results/stage4-tu.DONE").read_text().strip() if (r / "results/stage4-tu.DONE").exists() else "-"
        summ = r / "results/stage4/test-u-k5/run/summary.json"
        verdict = json.loads(summ.read_text())["verdict"] if summ.exists() else "-"
        check(done == "0" and verdict == "ALL CLOSED", f"test-u: DONE={done}, {verdict}")
        nrec = len((r / "results/stage4/test-u-k5/run/results.jsonl").read_text().splitlines())
        # 3. resume
        p = run(drv + ["stage4-tu", "2", "1"], r, dict(env, STAGE4_NAMES="test-u-k5"))
        nrec2 = len((r / "results/stage4/test-u-k5/run/results.jsonl").read_text().splitlines())
        done = (r / "results/stage4-tu.DONE").read_text().strip()
        check(done == "0" and nrec2 == nrec and "already ALL CLOSED" in p.stdout,
              f"rerun resumes ({nrec} -> {nrec2} records, DONE={done})")
        # 2b. queue longer than the slots: two instances through one slot
        p = run(drv + ["stage4-tq", "2", "1"], r, dict(env, SLOTS="1", STAGE4_NAMES="test-u-k5 test-v-k5"))
        done = (r / "results/stage4-tq.DONE").read_text().strip()
        check(done == "0" and "test-u-k5 already ALL CLOSED" in p.stdout and "conquer test-v-k5 finished" in p.stdout
              and "test-v-k5 ALL CLOSED" in p.stdout and "test-u-k5 ALL CLOSED" in p.stdout,
              f"queue through one slot: DONE={done}")
        # 3c. defaults: all instances side by side, timeouts 1800,3600,1800,7200,0 (both instances closed already)
        envd = {k: v for k, v in os.environ.items() if k not in ("SLOTS", "TIMEOUTS")}
        envd.update(POLL="1", STAGE4_NAMES="test-u-k5 test-v-k5")
        p = subprocess.run(drv + ["stage4-td", "4", "1"], cwd=r, env=envd, capture_output=True, text=True)
        done = (r / "results/stage4-td.DONE").read_text().strip()
        check(done == "0" and "2 instances, 2 side by side with 2 workers each, timeouts 1800,3600,1800,7200,0" in p.stdout,
              f"defaults: all instances side by side, timeouts 1800,3600,1800,7200,0 (DONE={done}): "
              + next((l for l in p.stdout.splitlines() if "instances," in l), p.stdout[-300:]))
        # 2c. failed LRAT checks are reported and the stage does not close
        p = run(drv + ["stage4-te", "2", "1"], r, dict(env, STAGE4_NAMES="test-e-k5"))
        done = (r / "results/stage4-te.DONE").read_text().strip()
        check(done == "1" and "LRAT CHECK FAILED in test-e-k5" in p.stdout and "test-e-k5 NOT CLOSED" in p.stdout,
              f"failed LRAT check reported, NOT CLOSED (DONE={done})")
        # 4. SAT instance stops the stage
        p = run(drv + ["stage4-ts", "2", "1"], r, dict(env, STAGE4_NAMES="test-s-k5 test-u-k5"))
        done = (r / "results/stage4-ts.DONE").read_text().strip()
        sat = (r / "results/stage4-ts.SAT")
        txt = sat.read_text() if sat.exists() else ""
        check(done == "1" and "SAT CUBE in test-s-k5" in txt and "TT5-free OK" in txt and "verify_model exit 0" in txt
              and "STOPPING THE STAGE" in p.stdout, f"SAT found, model verified, stage stopped (DONE={done})")
        p = run(drv + ["stage4-ts", "2", "1"], r, dict(env, STAGE4_NAMES="test-s-k5 test-u-k5"))
        check("not starting" in p.stdout, "rerun after SAT refuses to start")
        # 6. corrupted model rejected
        model = next((r / "results/stage4/test-s-k5/run").glob("SAT_*.model"))
        lits = [int(x) for x in model.read_text().split()]
        free = [i for i, l in enumerate(lits) if l != 0][:1]
        bad_model = r / "bad.model"
        bad_model.write_text(" ".join(str(-l) if i in free else str(l) for i, l in enumerate(lits)))
        p = run([sys.executable, "scripts/verify_model.py", "--numbering", "nmh", "--model", str(bad_model),
                 "--out", str(r / "m"), "data/test-s-k5.txt", "cnf/stage4/test-s-k5.cnf", "5"], r)
        check(p.returncode != 0, f"corrupted model rejected ({p.stdout.strip()[:80]})")
        # 5. sha256 mismatch refused
        man["instances"]["test-u-k5"]["cnf_sha256"] = "0" * 64
        (r / "data/stage4_manifest.json").write_text(json.dumps(man))
        shutil.rmtree(r / "results/stage4/test-u-k5")
        p = run(drv + ["stage4-tx", "2", "1"], r, dict(env, STAGE4_NAMES="test-u-k5"))
        done = (r / "results/stage4-tx.DONE").read_text().strip()
        check(done == "1" and "PREPARE FAILED for test-u-k5" in p.stdout, f"sha256 mismatch refused (DONE={done})")
    print("OK" if bad == 0 else f"FAILED ({bad})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
