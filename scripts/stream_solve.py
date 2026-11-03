"""Solve CNF-body + extra clauses with CaDiCaL and check its LRAT proof on the fly.

Nothing large touches the disk: the formula (header + a shared body file +
per-call extra clauses, e.g. cube units or blocking clauses) is streamed through
named pipes into CaDiCaL and into lrat-check, and CaDiCaL's text LRAT proof is
streamed through a third pipe into lrat-check (as in kobon/scripts/run_cubes.py,
which wrote the CNF to disk instead).  Clause ids in the proof refer to the
streamed order, which both readers see identically.

API: stream_solve(body_path, nvars, nbody, extra_lines, workdir, tag,
                  timeout=0, check=True) -> dict(status, secs, check, model)
  body_path : file with clause lines only (no 'p cnf' header), nbody clauses
  extra_lines: list of clause strings "l1 l2 ... 0"
CLI (one-off): stream_solve.py CNF [--timeout S] [--units "l1 l2 ..."]
"""
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LRAT_CHECK = str(ROOT / "build/lrat-check")
CADICAL = os.environ.get("CADICAL", "cadical")


def _writer(fifo, header, body_path, extra):
    try:
        with open(fifo, "w") as fh:
            fh.write(header)
            if body_path:
                with open(body_path) as src:
                    shutil.copyfileobj(src, fh, 1 << 20)
            fh.write(extra)
    except BrokenPipeError:
        pass


def stream_solve(body_path, nvars, nbody, extra_lines, workdir, tag, timeout=0, check=True, nice=10):
    os.makedirs(workdir, exist_ok=True)
    d = tempfile.mkdtemp(prefix=f"ss_{tag}_", dir=workdir)
    extra = "".join(l if l.endswith("\n") else l + "\n" for l in extra_lines)
    header = f"p cnf {nvars} {nbody + len(extra_lines)}\n"
    f_in = os.path.join(d, "in.cnf")
    os.mkfifo(f_in)
    threads = [threading.Thread(target=_writer, args=(f_in, header, body_path, extra), daemon=True)]
    cmd = ["nice", "-n", str(nice), CADICAL, "-q"]
    if timeout:
        cmd += ["-t", str(timeout)]
    chk = None
    if check:
        f_chk = os.path.join(d, "chk.cnf")
        f_prf = os.path.join(d, "proof.lrat")
        os.mkfifo(f_chk)
        os.mkfifo(f_prf)
        threads.append(threading.Thread(target=_writer, args=(f_chk, header, body_path, extra), daemon=True))
        chk = subprocess.Popen(["nice", "-n", str(nice), LRAT_CHECK, f_chk, f_prf],
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        cmd += ["--lrat=true", "--binary=false", f_in, f_prf]
    else:
        cmd += [f_in]
    for t in threads:
        t.start()
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    secs = round(time.time() - t0, 2)
    status = {10: "SAT", 20: "UNSAT"}.get(r.returncode, "UNKNOWN")
    rec = {"status": status, "secs": secs}
    if status == "SAT":
        rec["model"] = [int(x) for l in r.stdout.splitlines() if l.startswith("v") for x in l.split()[1:]]
    if chk is not None:
        out, _ = chk.communicate()
        rec["check_secs"] = round(time.time() - t0, 2)
        if status == "UNSAT":
            rec["check"] = "VERIFIED" if "c VERIFIED" in out else "FAILED"
    for t in threads:
        t.join(timeout=5)
    shutil.rmtree(d, ignore_errors=True)
    return rec


def split_cnf(cnf_path, body_path):
    """Write the clause lines of a DIMACS file (header dropped) to body_path; return (nv, nc)."""
    with open(cnf_path) as src, open(body_path, "w") as dst:
        h = src.readline().split()
        assert h[:2] == ["p", "cnf"], h
        shutil.copyfileobj(src, dst, 1 << 20)
    return int(h[2]), int(h[3])


if __name__ == "__main__":
    cnf = sys.argv[1]
    timeout = int(sys.argv[sys.argv.index("--timeout") + 1]) if "--timeout" in sys.argv else 0
    units = sys.argv[sys.argv.index("--units") + 1].split() if "--units" in sys.argv else []
    wd = tempfile.mkdtemp(prefix="ss_")
    body = os.path.join(wd, "body.cnf")
    nv, nc = split_cnf(cnf, body)
    rec = stream_solve(body, nv, nc, [f"{u} 0" for u in units], wd, "cli", timeout)
    shutil.rmtree(wd, ignore_errors=True)
    rec.pop("model", None)
    print(rec)
