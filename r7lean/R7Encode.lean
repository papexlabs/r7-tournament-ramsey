import R7lean.Enc.NMH
import R7lean.Enc.Tri
import R7lean.Enc.Dimacs
import R7lean.Enc.Instances

/-!
# `lake exe r7encode`: write the CNFs of the Lean encoders and compare their sha256

```
lake exe r7encode list
lake exe r7encode run NAME... [--dir DIR] [--keep]     # NAME: as in the manifests, or `stage4`, `stage3`
lake exe r7encode matrix FILE B nmh|tri OUT            # test mode: a pivot matrix file with |Z| = B
```

`run` writes `DIR/NAME.cnf` (default `DIR = .`), i.e. `NMH.cnf spec` or `Tri.cnf spec` of
`R7lean/Enc/Instances.lean` in DIMACS format with the header of the manifest, runs
`shasum -a 256` on it and compares sha256, clause count and byte count with the manifest
(`data/stage4_manifest.json`, `data/stage3_manifest.json`); the file is deleted unless `--keep`.
It also prints the number of generated items that failed a certified check (must be `0`).

This is a compiled run: it evaluates the same Lean functions (`NMH.step`, `Tri.step`,
`checkItem`, the contexts) that define the CNFs in the kernel; see `R7lean/Enc/Dimacs.lean`.
-/

open R7.Enc R7.Enc.Inst

def encodeSpec (enc : Encoder) (spec : PivotSpec) (headerVars : Option Nat)
    (out : System.FilePath) (progress : Nat → Nat → IO Unit) : IO Stats :=
  match enc with
  | .nmh =>
    let e := NMH.env spec
    let nb := NMH.nblocks e
    writeCNF out headerVars (NMH.ctx spec) 7 (NMH.step e) () nb (fun _ => 0) (progress nb)
  | .tri =>
    let e := Tri.env spec
    -- first pass: the 3-cycle variables (`Tri.final`), which fix the context
    let st := Tri.final spec
    let nb := Tri.nblocks e
    writeCNF out (some (headerVars.getD st.nv)) (Tri.ctxOf spec e st) 7 (Tri.step e)
      (Tri.St.init e) nb (fun _ => st.nv) (progress nb)

def sha256File (p : System.FilePath) : IO String := do
  let r ← IO.Process.output { cmd := "shasum", args := #["-a", "256", p.toString] }
  return (r.stdout.splitOn " ").headD ""

def noProgress (_ _ : Nat) : IO Unit := pure ()

def runEntry (dir : System.FilePath) (keep : Bool) (e : Entry) : IO Bool := do
  let out := dir / (e.name ++ ".cnf")
  let t0 ← IO.monoMsNow
  let progress (nb i : Nat) : IO Unit := do
    if (i + 1) % 100 == 0 || i + 1 == nb then
      let t ← IO.monoMsNow
      IO.eprintln s!"  {e.name}: block {i + 1}/{nb}, {(t - t0) / 1000} s"
  let stats ← encodeSpec e.enc e.spec e.headerVars out progress
  let t1 ← IO.monoMsNow
  let h ← sha256File out
  let size := (← out.metadata).byteSize
  let ok := h == e.sha256 && stats.written == e.clauses && size.toNat == e.bytes && stats.failed == 0
  IO.println s!"{e.name}: sha256 {h} {if h == e.sha256 then "MATCH" else "MISMATCH"} | clauses {stats.written} (manifest {e.clauses}) | bytes {size} (manifest {e.bytes}) | failed checks {stats.failed} | {(t1 - t0) / 1000} s | {if ok then "OK" else "FAIL"}"
  if !keep then IO.FS.removeFile out
  return ok

/-- Test mode: the pivot instance of a matrix file (`0`/`1`/`*`, upper triangle read). -/
def specOfMatrix (path : System.FilePath) (b : Nat) : IO PivotSpec := do
  let s ← IO.FS.readFile path
  let s' := s.map fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c
  let toks := ((s'.splitOn " ").filter (· ≠ "")).toArray
  let n := Nat.sqrt toks.size
  if n * n != toks.size then throw <| IO.userError "not square"
  let a := n - 1 - b
  let rowsOf (off m : Nat) : List Nat := (List.range m).map fun i =>
    (List.range m).foldl (fun acc j =>
      if toks[(off + i) * n + (off + j)]! == "1" then acc ||| (1 <<< j) else acc) 0
  return ⟨a, b, upperArc (rowsOf 0 a), upperArc (rowsOf (a + 1) b)⟩

def usage : String :=
  "usage: r7encode list | run NAME... [--dir DIR] [--keep] | matrix FILE B nmh|tri OUT"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for e in entries do
      IO.println s!"{e.name} {repr e.enc} {e.sha256}"
    return 0
  | "run" :: rest =>
    let mut dir : System.FilePath := "."
    let mut keep := false
    let mut names : Array String := #[]
    let mut r := rest
    for _ in [0:rest.length] do
      match r with
      | "--dir" :: d :: r' => dir := d; r := r'
      | "--keep" :: r' => keep := true; r := r'
      | x :: r' => names := names.push x; r := r'
      | [] => break
    let sel := entries.filter fun e =>
      names.contains e.name || (names.contains "stage4" && e.enc == .nmh) ||
        (names.contains "stage3" && e.enc == .tri)
    if sel.isEmpty then
      IO.eprintln usage
      return 1
    let mut allOk := true
    for e in sel do
      let ok ← runEntry dir keep e
      allOk := allOk && ok
    return if allOk then 0 else 1
  | ["matrix", file, b, enc, out] =>
    let spec ← specOfMatrix file b.toNat!
    let n := spec.n
    let nmhVars := n * (n - 1) / 2 + n * (n - 1) * (n - 2) / 6
    let stats ← if enc == "nmh" then encodeSpec .nmh spec (some nmhVars) out noProgress
      else encodeSpec .tri spec none out noProgress
    IO.println s!"clauses {stats.written} failed checks {stats.failed}"
    return 0
  | _ =>
    IO.eprintln usage
    return 1
