"""certify-first path == classic path on the complete TT5-free runs, plus a negative test.

For n = 10..13 (k = 5): certify_first.py, then pivot_enum.py (aggregation only)
and certify_enum.py; the classes must equal data/tt5free/tt5free{n}.d6, every
job complete and VERIFIED.  Negative tests: drop one model of a SAT job (and its
certificate) and re-certify; certify_enum must report that job as not verified.
Reverse one arc inside A of one model (the model no longer fits its job): the job
must be MODEL_MISMATCH and not verified.
k = 6, n = 26 (one job, 39 models): exactly one class, ST27 minus a vertex (ST26).
Run: python3 tests/test_certify_first.py
"""
import json, shutil, subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
PY = sys.executable
bad = 0
td = Path(tempfile.mkdtemp(prefix="tcf_"))
for n in (10, 11, 12, 13):
    d = td / f"k5n{n}"
    subprocess.run([PY, str(ROOT / "scripts/certify_first.py"), "5", str(n), str(d), "--workers", "2"], check=True, capture_output=True)
    subprocess.run([PY, str(ROOT / "scripts/pivot_enum.py"), "5", str(n), str(d)], check=True, capture_output=True)
    subprocess.run([PY, str(ROOT / "scripts/certify_enum.py"), str(d), "--workers", "2"], check=True, capture_output=True)
    s = json.loads((d / "summary.json").read_text()); c = json.loads((d / "certify_summary.json").read_text())
    log = [json.loads(l) for l in (d / "certify_first.jsonl").read_text().splitlines()]
    cls = (d / "classes.d6").read_text().split()
    ok = s["all_complete"] and c["all_jobs_verified"] and cls == (ROOT / f"data/tt5free/tt5free{n}.d6").read_text().split()
    bad += not ok
    print(f"n={n}: jobs={s['jobs_total']} first-UNSAT-verified={sum(x['status']=='UNSAT' and x['check']=='VERIFIED' for x in log)} "
          f"fallback={sum(not (x['status']=='UNSAT' and x['check']=='VERIFIED') for x in log)} classes={len(cls)} "
          f"all_complete={s['all_complete']} all_verified={c['all_jobs_verified']} identical={ok}")
# negative test on n=10 (has SAT jobs)
src = td / "k5n10"; neg = td / "neg"; shutil.copytree(src, neg)
recs = [json.loads(l) for l in (neg / "records.jsonl").read_text().splitlines()]
victim = next(r for r in recs if r["models"] > 0)
key = (victim["d"], victim["ia"], victim["ib"])
removed = False
for p in sorted((neg / "models").glob("*.d6")):
    lines = p.read_text().splitlines(); keep = []
    for l in lines:
        f = l.split()
        if not removed and (int(f[0]), int(f[1]), int(f[2])) == key:
            removed = True; continue
        keep.append(l)
    p.write_text("\n".join(keep) + ("\n" if keep else ""))
for r in recs:
    if (r["d"], r["ia"], r["ib"]) == key: r["models"] -= 1
(neg / "records.jsonl").write_text("".join(json.dumps(r) + "\n" for r in recs))
certs = [json.loads(l) for l in (neg / "certify.jsonl").read_text().splitlines()]
(neg / "certify.jsonl").write_text("".join(json.dumps(c) + "\n" for c in certs if (c["d"], c["ia"], c["ib"]) != key))
subprocess.run([PY, str(ROOT / "scripts/certify_enum.py"), str(neg), "--workers", "2"], check=True, capture_output=True)
c = json.loads((neg / "certify_summary.json").read_text())
caught = not c["all_jobs_verified"]
bad += not caught
print(f"negative test (one model of job {key} dropped): caught={caught}")
# negative test 2 on n=10: a model whose arcs inside A differ from its job's catalogue line
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402
neg2 = td / "neg2"; shutil.copytree(src, neg2)
p = sorted((neg2 / "models").glob("*.d6"))[0]
lines = p.read_text().splitlines(); f = lines[0].split(); key2 = (int(f[0]), int(f[1]), int(f[2]))
o = T.from_d6(f[3]); o[0] ^= 1 << 1; o[1] ^= 1 << 0   # reverse the arc between vertices 0 and 1 (both in A)
f[3] = T.to_d6(o); lines[0] = " ".join(f); p.write_text("\n".join(lines) + "\n")
certs = [json.loads(l) for l in (neg2 / "certify.jsonl").read_text().splitlines()]
(neg2 / "certify.jsonl").write_text("".join(json.dumps(c) + "\n" for c in certs if (c["d"], c["ia"], c["ib"]) != key2))
subprocess.run([PY, str(ROOT / "scripts/certify_enum.py"), str(neg2), "--workers", "2"], check=True, capture_output=True)
c = json.loads((neg2 / "certify_summary.json").read_text())
last = [json.loads(l) for l in (neg2 / "certify.jsonl").read_text().splitlines() if (json.loads(l)["d"], json.loads(l)["ia"], json.loads(l)["ib"]) == key2]
caught = not c["all_jobs_verified"] and c["model_mismatch_jobs"] == 1 and last and last[-1]["status"] == "MODEL_MISMATCH"
bad += not caught
print(f"negative test (model of job {key2} with a reversed arc inside A): caught={caught}")
# k = 6, n = 26: ST26 is the only TT6-free tournament on 26 vertices
d = td / "k6n26"
subprocess.run([PY, str(ROOT / "scripts/certify_first.py"), "6", "26", str(d), "--workers", "2"], check=True, capture_output=True)
subprocess.run([PY, str(ROOT / "scripts/pivot_enum.py"), "6", "26", str(d)], check=True, capture_output=True)
subprocess.run([PY, str(ROOT / "scripts/certify_enum.py"), str(d), "--workers", "2"], check=True, capture_output=True)
s = json.loads((d / "summary.json").read_text()); c = json.loads((d / "certify_summary.json").read_text())
cls = (d / "classes.d6").read_text().split()
st27 = T.matrix_to_out(T.read_matrix(ROOT / "data/ST27.txt"))
ok = (s["jobs_total"] == 1 and s["all_complete"] and c["all_jobs_verified"] and len(cls) == 1
      and T.canon(T.from_d6(cls[0])) == T.canon(T.induced(st27, list(range(26)))))
bad += not ok
print(f"k=6 n=26: jobs={s['jobs_total']} models={s['raw_models']} classes={len(cls)} complete={s['all_complete']} "
      f"verified={c['all_jobs_verified']} one class = ST27 minus a vertex: {ok}")
shutil.rmtree(td, ignore_errors=True)
print("FAIL" if bad else "ALL OK"); sys.exit(1 if bad else 0)
