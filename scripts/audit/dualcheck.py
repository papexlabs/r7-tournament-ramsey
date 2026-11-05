"""Second proof check: run the patched lrat-check and the formally verified cake_lpr side by side.

usage: dualcheck.sh CNF PROOF        (scripts/audit/dualcheck.sh runs this file with python3 -I)

A drop-in replacement for build/lrat-check, usable as scripts/stream_solve.py's LRAT_CHECK.
CNF and PROOF may be named pipes (stream_solve gives FIFOs).  Each is read once and copied
(tee) into two anonymous pipes, one per checker; the checkers open them as /dev/fd/N, so no
open() can block on a missing reader.  The two copies of a stream are written in lock step,
so the faster checker waits for the slower one (CaDiCaL waits for both, as it waits for
lrat-check alone).

Verdict: prints "c VERIFIED" and exits 0 only if
  - lrat-check is VERIFIED by stream_solve.lrat_verdict (exit 0, a "c VERIFIED" line, no "FAILED",
    no "NOT VERIFIED"), AND
  - cake_lpr exited 0 and printed exactly the one stdout line "s VERIFIED UNSAT" and nothing on
    stderr (cake_lpr exits 0 even when the check fails: the text is the verdict).
Otherwise it prints "c NOT VERIFIED" and exits 1.  One line per checker ("c lrat-check: ...",
"c cake_lpr: ...") says what each said.

Early exit: a checker that exits (or dies) closes its pipes; the copy to it stops and the copy to
the other continues.  When a checker exits with a failed verdict, the other is killed (it then
fails too) unless DUALCHECK_KEEP_GOING=1, and when no checker reads a stream any more the input is
closed, so the writer (CaDiCaL) gets EPIPE as with lrat-check alone.  Nothing waits forever on a
checker that has gone.

Environment (all optional):
  DUALCHECK_LRAT        lrat-check binary   (default build/lrat-check)
  DUALCHECK_CAKE        cake_lpr binary     (default build/cake_lpr)
  DUALCHECK_CAKE_HEAP   cake_lpr heap in MiB  (--CML_HEAP_SIZE=; cake_lpr's default is 4096)
  DUALCHECK_CAKE_STACK  cake_lpr stack in MiB (--CML_STACK_SIZE=; default 4096)
  DUALCHECK_LOG_DIR     write one JSON log per call there: both verdicts, exit codes, CPU seconds,
                        peak RSS and the last DUALCHECK_TAIL (default 20) lines of each checker's
                        output.  The file is named after the CNF's directory (stream_solve's
                        ss_<tag>_<random>), else after the CNF file name, plus .json.
  DUALCHECK_KEEP_GOING  1: let the other checker finish after one has failed.
  DUALCHECK_REQUIRE     both (default): VERIFIED only if both checkers verify.  lrat: the verdict
                        is lrat-check's alone (strict rule); cake_lpr still runs to the end and
                        its verdict is only logged (use with DUALCHECK_LOG_DIR), so a cake_lpr
                        failure such as an exhausted heap never stops a long run; the logs are
                        checked afterwards and failed items re-checked.
"""
import json
import os
import queue
import resource
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from stream_solve import lrat_verdict  # noqa: E402

CAKE_OK = "s VERIFIED UNSAT"
CHUNK = 1 << 20


def cake_verdict(returncode, stdout, stderr):
    """'VERIFIED' iff cake_lpr exited 0, its stdout is exactly the line 's VERIFIED UNSAT' and stderr is empty."""
    ok = returncode == 0 and stdout.splitlines() == [CAKE_OK] and stderr.strip() == ""
    return "VERIFIED" if ok else "FAILED"


def rss_gb(ru):
    return round(ru.ru_maxrss / (2**30 if sys.platform == "darwin" else 2**20), 3)


class Tee(threading.Thread):
    """Copy one input (file or FIFO) to several pipe write ends; a broken output is dropped."""

    def __init__(self, name, path, outs):
        super().__init__(daemon=True, name=name)
        self.path, self.outs = path, dict(outs)      # checker name -> write fd
        self.sent = {k: 0 for k in self.outs}
        self.total = 0
        self.closed_early = False
        self.error = None
        self.lock = threading.Lock()
        self.opened = threading.Event()        # set once the input is open (or could not be opened)

    def drop(self, k):
        with self.lock:
            fd = self.outs.pop(k, None)
        if fd is not None:
            try:
                os.close(fd)
            except OSError:
                pass

    def run(self):
        fd = None
        try:
            try:
                fd = os.open(self.path, os.O_RDONLY)
            finally:
                self.opened.set()
            while True:
                with self.lock:
                    live = list(self.outs.items())
                if not live:                   # nobody reads any more: let the writer see EPIPE
                    self.closed_early = True
                    break
                buf = os.read(fd, CHUNK)
                if not buf:
                    break
                self.total += len(buf)
                for k, w in live:
                    mv = memoryview(buf)
                    try:
                        while mv:
                            n = os.write(w, mv)
                            mv = mv[n:]
                        self.sent[k] += len(buf)
                    except OSError:            # EPIPE (checker gone) or EBADF (dropped meanwhile)
                        self.drop(k)
        except OSError as e:
            self.error = f"{type(e).__name__}: {e}"
        finally:
            for k in list(self.outs):
                self.drop(k)
            if fd is not None:
                os.close(fd)


def spawn(cmd, fds):
    out = tempfile.TemporaryFile()
    err = tempfile.TemporaryFile()
    p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=out, stderr=err, pass_fds=fds, close_fds=True)
    return p, out, err


def read_back(fh):
    fh.seek(0)
    return fh.read().decode("utf-8", "replace")


def tail(text, n):
    return text.splitlines()[-n:]


def pick_said(lines):
    """The most telling output line: a failure, else a verdict line, else the last line."""
    for keys in (("FAILED", "failed", "exhausted", "ERROR", "rror", "not derived"), ("VERIFIED",)):
        for l in lines:
            if any(k in l for k in keys):
                return l.strip()
    return next((l.strip() for l in reversed(lines) if l.strip()), "(no output)")


def log_name(cnf):
    parent = Path(cnf).resolve().parent.name
    base = parent if parent.startswith("ss_") else Path(cnf).name
    return f"{base}.{os.getpid()}.json"


def main(argv):
    if len(argv) != 3:
        print("usage: dualcheck.sh CNF PROOF")
        print("c NOT VERIFIED")
        return 1
    cnf, proof = argv[1], argv[2]
    t0 = time.time()
    lrat_bin = os.environ.get("DUALCHECK_LRAT", str(ROOT / "build/lrat-check"))
    cake_bin = os.environ.get("DUALCHECK_CAKE", str(ROOT / "build/cake_lpr"))
    cake_flags = []
    if os.environ.get("DUALCHECK_CAKE_HEAP"):
        cake_flags.append(f"--CML_HEAP_SIZE={int(os.environ['DUALCHECK_CAKE_HEAP'])}")
    if os.environ.get("DUALCHECK_CAKE_STACK"):
        cake_flags.append(f"--CML_STACK_SIZE={int(os.environ['DUALCHECK_CAKE_STACK'])}")
    require = os.environ.get("DUALCHECK_REQUIRE", "both")
    if require not in ("both", "lrat"):
        print(f"c NOT VERIFIED: unknown DUALCHECK_REQUIRE={require}", flush=True)
        return 1
    keep_going = os.environ.get("DUALCHECK_KEEP_GOING") == "1" or require == "lrat"
    ntail = int(os.environ.get("DUALCHECK_TAIL", "20"))

    names = ("lrat-check", "cake_lpr")
    pipes = {k: {"cnf": os.pipe(), "proof": os.pipe()} for k in names}   # (read, write)
    procs, files, info = {}, {}, {}
    for k, binary, flags in (("lrat-check", lrat_bin, []), ("cake_lpr", cake_bin, cake_flags)):
        rc_, rp = pipes[k]["cnf"][0], pipes[k]["proof"][0]
        cmd = [binary] + flags + [f"/dev/fd/{rc_}", f"/dev/fd/{rp}"]
        info[k] = {"cmd": " ".join([Path(binary).name] + flags)}
        try:
            procs[k], out, err = spawn(cmd, (rc_, rp))
            files[k] = (out, err)
        except OSError as e:
            info[k].update(verdict="FAILED", exit=None, said=f"could not start: {e}", tail=[])
        os.close(rc_)
        os.close(rp)
    for k in names:
        if k not in procs:                     # its copies have no reader: close the write ends now
            os.close(pipes[k]["cnf"][1])
            os.close(pipes[k]["proof"][1])
    tees = [Tee("cnf", cnf, {k: pipes[k]["cnf"][1] for k in procs}),
            Tee("proof", proof, {k: pipes[k]["proof"][1] for k in procs})]
    for t in tees:
        t.start()
    # Only the waiter threads reap the checkers (os.wait4, for their CPU time and peak RSS), so a
    # pid stays ours until its waiter has returned: os.kill is safe until then.  (Popen.poll or
    # send_signal would reap it behind the waiter's back.)
    started = {k: time.time() for k in procs}
    done = queue.Queue()

    def waiter(k, p):
        try:
            _, status, ru = os.wait4(p.pid, 0)
            p.returncode = os.waitstatus_to_exitcode(status)
        except ChildProcessError:
            p.returncode, ru = -999, None
        done.put((k, ru))

    def kill(q):
        if q.returncode is None:
            try:
                os.kill(q.pid, signal.SIGTERM)
            except OSError:
                pass

    if len(procs) < len(names) and not keep_going:   # a checker did not start: the verdict is FAILED
        for q in procs.values():
            kill(q)

    for k, p in procs.items():
        threading.Thread(target=waiter, args=(k, p), daemon=True).start()
    killed = {}
    failed_first = None
    for _ in range(len(procs)):
        k, ru = done.get()
        p = procs[k]
        out_s, err_s = read_back(files[k][0]), read_back(files[k][1])
        if k == "lrat-check":
            v = lrat_verdict(p.returncode, out_s + err_s)
        else:
            v = cake_verdict(p.returncode, out_s, err_s)
        lines = tail(out_s + ("\n" if out_s and not out_s.endswith("\n") else "") + err_s, ntail)
        said = pick_said(lines)
        info[k].update(verdict=v, exit=p.returncode, secs=round(time.time() - started[k], 2),
                       cpu=round(ru.ru_utime + ru.ru_stime, 2) if ru else None, rss_gb=rss_gb(ru) if ru else None,
                       said=said, tail=lines)
        if k in killed:
            info[k]["killed_after"] = killed[k]
        if v != "VERIFIED" and failed_first is None:
            failed_first = k
            if not keep_going:
                for o, q in procs.items():
                    if o != k and q.returncode is None:
                        killed[o] = f"{k} failed"
                        kill(q)

    # Exit only once both inputs are open: a writer still waiting to open its FIFO (CaDiCaL, the
    # formula writer) would otherwise wait forever.  After we exit, its writes get EPIPE.
    for t in tees:
        t.opened.wait()
    both_ok = all(info[k]["verdict"] == "VERIFIED" for k in names)
    ok = both_ok if require == "both" else info["lrat-check"]["verdict"] == "VERIFIED"
    for k in names:
        extra = f" (killed after {info[k]['killed_after']})" if "killed_after" in info[k] else ""
        if require == "lrat" and k == "cake_lpr":
            # log-only: never print a failure word here, stream_solve's strict rule would read it
            print(f"c cake_lpr: logged only ({'ok' if info[k]['verdict'] == 'VERIFIED' else 'see log'})")
        elif info[k]["verdict"] == "VERIFIED":
            print(f"c {k}: VERIFIED (exit {info[k]['exit']})")
        else:
            print(f"c {k}: {info[k]['verdict']} (exit {info[k]['exit']}){extra}: {info[k]['said']}")
    print("c VERIFIED" if ok else "c NOT VERIFIED", flush=True)

    logdir = os.environ.get("DUALCHECK_LOG_DIR")
    if logdir:
        rec = {"verdict": "VERIFIED" if ok else "NOT VERIFIED", "require": require, "both_verified": both_ok,
               "secs": round(time.time() - t0, 2),
               "cnf": cnf, "proof": proof, "first_failure": failed_first,
               "bytes": {t.name: t.total for t in tees},
               "bytes_sent": {t.name: t.sent for t in tees},
               "input_closed_early": {t.name: t.closed_early for t in tees},
               "input_error": {t.name: t.error for t in tees if t.error},
               "lrat": info["lrat-check"], "cake": info["cake_lpr"], "t": time.strftime("%FT%T")}
        try:
            os.makedirs(logdir, exist_ok=True)
            path = Path(logdir) / log_name(cnf)
            tmp = path.with_suffix(".tmp")
            tmp.write_text(json.dumps(rec) + "\n")
            os.replace(tmp, path)
        except OSError as e:
            print(f"c log not written: {e}", file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    sys.exit(main(sys.argv))
