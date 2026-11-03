"""Per-run AWS cost meter and hard stop (Mac side, aws CLI, profile kobon, eu-north-1).

Reads results/aws_ledger.csv (one line per launched instance, written by
launch.sh), asks EC2 (read-only) for each instance's state and launch time, and
integrates the eu-north-1 spot price history of its type/AZ from launch to
termination (or now).  EBS is added at gp3 list price.  Prints per-instance,
per-stage and total estimated cost and keeps results/aws_cost.json.

--enforce: if the total reaches --cap (default 95 USD, leaving room under the
100 USD budget) or a stage reaches its own cap from the ledger, terminate that
stage's running instances (the only write call this script makes).
--loop SECONDS: repeat (e.g. every 600 s while a stage runs).

Credentials are never read or printed by this script; the aws CLI uses the
profile.  Note: this is an estimate from public spot prices; the bill (and the
credit balance, which the kobon IAM user cannot read) is the authority.
usage: python3 scripts/cloud/cost_meter.py [--enforce] [--cap 95] [--loop 600]
"""
import argparse
import csv
import datetime as dt
import json
import os
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "results/aws_ledger.csv"
STATE = ROOT / "results/aws_cost.json"
ENV = dict(os.environ, AWS_PROFILE="kobon", AWS_REGION="eu-north-1", AWS_PAGER="")
GP3_USD_PER_GB_HOUR = 0.0836 / 730  # eu-north-1 gp3 list price per GB-month


def aws(*args):
    r = subprocess.run(["aws", *args, "--output", "json"], capture_output=True, text=True, env=ENV)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[:300])
    return json.loads(r.stdout) if r.stdout.strip() else {}


def parse_t(s):
    return dt.datetime.fromisoformat(s.replace("Z", "+00:00"))


def spot_cost(itype, az, t0, t1):
    hist = aws("ec2", "describe-spot-price-history", "--instance-types", itype,
               "--availability-zone", az, "--product-descriptions", "Linux/UNIX",
               "--start-time", t0.isoformat(), "--end-time", t1.isoformat())["SpotPriceHistory"]
    pts = sorted((parse_t(h["Timestamp"]), float(h["SpotPrice"])) for h in hist)
    if not pts:
        return None
    if pts[0][0] > t0:  # no point at the start: charge the first known price from t0 (conservative)
        pts.insert(0, (t0, pts[0][1]))
    cost = 0.0
    for i, (ts, p) in enumerate(pts):
        a = max(ts, t0)
        b = pts[i + 1][0] if i + 1 < len(pts) else t1
        b = min(b, t1)
        if b > a:
            cost += p * (b - a).total_seconds() / 3600
    return cost


def measure(enforce, cap):
    if not LEDGER.exists():
        print("no ledger yet")
        return
    state = json.loads(STATE.read_text()) if STATE.exists() else {"instances": {}}
    rows = list(csv.DictReader(open(LEDGER)))
    now = dt.datetime.now(dt.timezone.utc)
    per_stage, total = {}, 0.0
    for row in rows:
        iid = row["instance_id"]
        st = state["instances"].setdefault(iid, {})
        try:
            res = aws("ec2", "describe-instances", "--instance-ids", iid)["Reservations"]
            inst = res[0]["Instances"][0] if res else None
        except RuntimeError:
            inst = None  # terminated long ago: keep the last known end time
        if inst:
            st["state"] = inst["State"]["Name"]
            st["az"] = inst["Placement"]["AvailabilityZone"]
            st["launch"] = inst["LaunchTime"]
            if st["state"] in ("running", "pending", "stopping", "shutting-down"):
                st["end"] = now.isoformat()
            elif "end" not in st:
                st["end"] = now.isoformat()
        if "launch" not in st:
            continue
        t0, t1 = parse_t(st["launch"]), parse_t(st["end"])
        c = spot_cost(row["instance_type"], st["az"], t0, t1)
        if c is None:  # no price points: bound by the max price
            c = float(row["max_price"]) * (t1 - t0).total_seconds() / 3600
        hours = (t1 - t0).total_seconds() / 3600
        c += GP3_USD_PER_GB_HOUR * float(row["disk_gb"]) * hours
        st["usd"] = round(c, 3)
        st["hours"] = round(hours, 2)
        per_stage[row["stage"]] = per_stage.get(row["stage"], 0.0) + c
        total += c
    state["per_stage_usd"] = {k: round(v, 2) for k, v in per_stage.items()}
    state["total_usd"] = round(total, 2)
    state["updated"] = now.isoformat()
    STATE.write_text(json.dumps(state, indent=1))
    print(json.dumps({"total_usd": state["total_usd"], "per_stage_usd": state["per_stage_usd"],
                      "instances": {k: {x: v.get(x) for x in ("state", "hours", "usd")}
                                    for k, v in state["instances"].items()}}))
    if enforce:
        for row in rows:
            st = state["instances"].get(row["instance_id"], {})
            over_total = total >= cap
            over_stage = per_stage.get(row["stage"], 0.0) >= float(row["stage_cap"])
            if st.get("state") in ("running", "pending") and (over_total or over_stage):
                print(f"HARD STOP: terminating {row['instance_id']} (total {total:.2f} / stage "
                      f"{per_stage.get(row['stage'], 0):.2f} of cap {row['stage_cap']})")
                aws("ec2", "terminate-instances", "--instance-ids", row["instance_id"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--enforce", action="store_true")
    ap.add_argument("--cap", type=float, default=95.0)
    ap.add_argument("--loop", type=int, default=0)
    a = ap.parse_args()
    while True:
        try:
            measure(a.enforce, a.cap)
        except Exception as e:  # keep looping through transient API errors
            print(f"{dt.datetime.now().isoformat()} meter error: {e}")
        if not a.loop:
            break
        time.sleep(a.loop)


if __name__ == "__main__":
    main()
