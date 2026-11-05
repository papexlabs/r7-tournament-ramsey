import R7lean.Enc.Basic

/-!
# Writing a block-structured CNF in DIMACS format (no Mathlib)

`writeBlocks h ctx k step s nb` runs exactly the loop of `runBlocks step s 0 nb` and writes,
for each item that passes `checkItem ctx k`, its clause as `l₁ l₂ … 0\n` (each literal followed
by a space, as `printf("%i ", l)` / `fprintf("%d ", l)` in the C encoders), i.e. it writes
`cnfOf ctx k (runBlocks step s 0 nb)` clause by clause without building the list. The header
`p cnf V C` is written by `writeCNF` once `C` (the number of clauses written) is known: the body
goes to `<out>.body` first and is then appended to the header (as `src/encode.c` does).
-/

namespace R7.Enc

/-- Append the decimal digits of `n`. -/
def pushNat (buf : ByteArray) (n : Nat) : ByteArray := Id.run do
  if n == 0 then return buf.push 48
  let mut digits : Array UInt8 := #[]
  let mut m := n
  for _ in [0:40] do
    if m == 0 then break
    digits := digits.push (48 + (m % 10).toUInt8)
    m := m / 10
  let mut buf := buf
  for i in [0:digits.size] do
    buf := buf.push digits[digits.size - 1 - i]!
  return buf

/-- Append a clause in DIMACS format. -/
def pushClause (buf : ByteArray) (cl : List Int) : ByteArray := Id.run do
  let mut buf := buf
  for l in cl do
    if l < 0 then buf := buf.push 45
    buf := pushNat buf l.natAbs
    buf := buf.push 32
  return (buf.push 48).push 10

structure Stats where
  written : Nat := 0
  failed : Nat := 0
  bytes : Nat := 0

/-- Write the clauses of the items of blocks `0, …, nb - 1` that pass the checks. -/
def writeBlocks {σ : Type} (h : IO.FS.Handle) (ctx : Ctx) (k : Nat)
    (step : σ → Nat → σ × Array (List Int × Just)) (s : σ) (nb : Nat)
    (progress : Nat → IO Unit := fun _ => pure ()) : IO Stats := do
  let mut st := s
  let mut buf := ByteArray.emptyWithCapacity (1 <<< 21)
  let mut stats : Stats := {}
  for i in [0:nb] do
    match step st i with
    | (st', out) =>
      st := st'
      for it in out do
        if checkItem ctx k it then
          buf := pushClause buf it.1
          stats := { stats with written := stats.written + 1 }
        else
          stats := { stats with failed := stats.failed + 1 }
      if buf.size > (1 <<< 20) then
        h.write buf
        stats := { stats with bytes := stats.bytes + buf.size }
        buf := ByteArray.emptyWithCapacity (1 <<< 21)
    progress i
  h.write buf
  return { stats with bytes := stats.bytes + buf.size }

/-- Write `p cnf V C` and the body: the body is written to `<out>.body` first. -/
def writeCNF {σ : Type} (out : System.FilePath) (vars : Option Nat) (ctx : Ctx) (k : Nat)
    (step : σ → Nat → σ × Array (List Int × Just)) (s : σ) (nb : Nat)
    (varsAfter : Unit → Nat) (progress : Nat → IO Unit := fun _ => pure ()) : IO Stats := do
  let bodyPath : System.FilePath := out.toString ++ ".body"
  let stats ← IO.FS.withFile bodyPath .write fun h => writeBlocks h ctx k step s nb progress
  let v := vars.getD (varsAfter ())
  IO.FS.withFile out .write fun h => do
    h.putStr s!"p cnf {v} {stats.written}\n"
    IO.FS.withFile bodyPath .read fun b => do
      for _ in [0:stats.bytes + 2] do
        let chunk ← b.read ((1 : USize) <<< 20)
        if chunk.isEmpty then break
        h.write chunk
  IO.FS.removeFile bodyPath
  return stats

end R7.Enc
