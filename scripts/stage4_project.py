"""Stage 4 cost projection from the Mac cube samples (notes/stage4/mac_samples.jsonl).

Per cube the cost is the CPU time (user + sys) of cadical plus lrat-check, as
measured by scripts/stage4_sample.py (rows without CPU time, from the first
pilot, use their wall time).  A cube still UNKNOWN at its time limit is counted
at twice the limit.

Per instance (2^K = 1024 level-0 cubes):
  sampled ST instances : 1024 x mean cube cost;
  23X-p-Y8             : ratio estimator over the sampled Y8 instances,
                         (sum of sampled 1024 x means) / (sum of their NMH conflicts) x conflicts_X.
Bootstrap (cubes resampled within instances) gives a 90% interval for the total.

Mac core-seconds -> Graviton4 vCPU-seconds: x G (2.5 central; one fully loaded
Graviton4 vCPU ran our jobs at ~0.4x an unloaded Mac core, 11-03; the Stage 3
cubes 463 and 886 of 24A took 227 / 221 s on the server against 94 s on the Mac).
Box hours = vCPU-h / (96 x U), U = 0.85 (scheduling tails, idle slots).

--write-manifest stores expected_vcpu_h per instance (the run order of run_stage4.sh; for
instances with >= 4 samples the average of their own estimate and the projection) and cube_k.
usage: stage4_project.py [--g 2.5] [--util 0.85] [--price 0.445] [--write-manifest]
"""
import argparse
import collections
import json
import random
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from stage4_instances import NAMES, MANIFEST  # noqa: E402

NCUBES = 1024


def cube_cost(r):
    c = r.get("cpu") or {}
    if c.get("cadical") is not None:
        v = c["cadical"] + (c.get("lrat-check") or 0)
    else:
        v = r["secs"]
    if r["status"] == "UNKNOWN":
        v = max(v, 2 * r["timeout"])
    return v


def project(samples, man, rng=None):
    """Mac core-seconds per instance (dict).  With rng: one bootstrap replicate."""
    by = collections.defaultdict(list)
    for r in samples:
        by[r["name"]].append(cube_cost(r))
    if rng:
        by = {n: [rng.choice(v) for _ in v] for n, v in by.items()}
    tot = {n: NCUBES * statistics.mean(v) for n, v in by.items()}
    y8 = [n for n in tot if n.endswith("-p-Y8")]
    conf = {n: man[n]["nmh_log"]["conflicts"] for n in NAMES if man[n].get("nmh_log")}
    ratio = sum(tot[n] for n in y8) / sum(conf[n] for n in y8)
    out = {}
    for n in NAMES:
        if n.endswith("-p-Y8"):
            out[n] = ratio * conf[n]
        elif n in tot:
            out[n] = tot[n]
        else:   # unsampled ST instance: ratio estimator on its conflicts
            out[n] = ratio * conf.get(n, max(conf.values()))
    return out, ratio, by


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--g", type=float, default=2.5)
    ap.add_argument("--util", type=float, default=0.85)
    ap.add_argument("--price", type=float, default=0.445)
    ap.add_argument("--write-manifest", action="store_true")
    a = ap.parse_args()
    samples = [json.loads(l) for l in open(ROOT / "notes/stage4/mac_samples.jsonl")]
    man_all = json.loads(MANIFEST.read_text())
    man = man_all["instances"]
    est, ratio, by = project(samples, man)
    rng = random.Random(46)
    boots = sorted(sum(project(samples, man, rng)[0].values()) for _ in range(2000))
    lo, hi = boots[int(0.05 * len(boots))], boots[int(0.95 * len(boots))]
    print(f"{'instance':12} {'samples':>7} {'unk':>3} {'mean s':>7} {'max s':>6} {'own Mac-h':>9} {'NMH Mconfl':>10} "
          f"{'proj Mac-h':>10} {'vCPU-h':>7} {'cad GB':>6} {'lrat GB':>7}")
    rows = []
    for n in NAMES:
        v = by.get(n, [])
        own = NCUBES * statistics.mean(v) / 3600 if v else None
        rs = [r for r in samples if r["name"] == n]
        unk = sum(r["status"] == "UNKNOWN" for r in rs)
        cg = max((r["rss_gb"].get("cadical") or 0 for r in rs), default=0)
        lg = max((r["rss_gb"].get("lrat-check") or 0 for r in rs), default=0)
        conf = man[n]["nmh_log"]["conflicts"] / 1e6 if man[n].get("nmh_log") else float("nan")
        mac_h = est[n] / 3600
        rows.append((n, mac_h))
        print(f"{n:12} {len(v):7d} {unk:3d} {statistics.mean(v) if v else 0:7.1f} {max(v) if v else 0:6.0f} "
              f"{own if own else 0:9.2f} {conf:10.0f} {mac_h:10.2f} {mac_h * a.g:7.1f} {cg:6.2f} {lg:7.2f}")
    # cross-check: unsampled Y8 instances at the plain mean of the sampled Y8 instances (ignores NMH conflicts)
    y8s = [n for n in by if n.endswith("-p-Y8")]
    mean_y8 = statistics.mean(NCUBES * statistics.mean(by[n]) for n in y8s)
    alt = sum((NCUBES * statistics.mean(by[n]) if n in by else (mean_y8 if n.endswith("-p-Y8") else est[n]))
              for n in NAMES) / 3600
    print(f"cross-check: sampled instances at their own mean, the rest at the sampled Y8 mean: {alt:.0f} Mac-core-h")
    tot_mac = sum(est.values()) / 3600
    vcpu = tot_mac * a.g
    box_h = vcpu / (96 * a.util)
    print(f"\nY8 ratio: {ratio * 1e6 / 3600:.3f} Mac-core-h per million NMH conflicts")
    print(f"total: {tot_mac:.0f} Mac-core-h (bootstrap 90%: {lo / 3600:.0f}-{hi / 3600:.0f}); "
          f"x{a.g} = {vcpu:.0f} vCPU-h central")
    for label, f in (("central", 1.0), ("bootstrap high", hi / sum(est.values())), ("tail (2x central)", 2.0),
                     ("tail with G=3", 2.0 * 3.0 / a.g)):
        bh = box_h * f
        print(f"  {label:18}: {vcpu * f:6.0f} vCPU-h, one 96-vCPU box {bh:5.1f} h, two boxes {bh / 2:5.1f} h, "
              f"US$ {bh * a.price:5.1f} (at {a.price}/h)")
    nsamp = sum(cube_cost(r) for r in samples) / 3600
    print(f"Mac CPU spent on these samples: {nsamp:.2f} core-h ({len(samples)} cubes)")
    if a.write_manifest:
        # for the run order only: sampled instances at the average of their own estimate and the projection
        for n, mac_h in rows:
            own = NCUBES * statistics.mean(by[n]) / 3600 if len(by.get(n, [])) >= 4 else mac_h
            man[n]["expected_vcpu_h"] = round((mac_h + own) / 2 * a.g, 1)
            man[n]["cube_k"] = 10
        MANIFEST.write_text(json.dumps(man_all, indent=1) + "\n")
        print("expected_vcpu_h written to", MANIFEST)


if __name__ == "__main__":
    main()
