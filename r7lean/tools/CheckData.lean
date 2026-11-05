import R7lean.Data

/-!
# Check the generated definitions against `data/`

Run from `r7lean/` with `lake env lean tools/CheckData.lean` (after `lake build`).

For every named tournament of `R7lean/Data.lean`, this reads the matrix file in `../data/`
at run time and compares every off-diagonal entry `(i, j)` (both triangles) with
`decide (T.beats i j)` as computed from the Lean definition. `ST26` is compared with `ST27`
minus vertex `0` and with the `X` block of `data/ST26-p-TT5.txt`; `ST25` with `ST27` minus
vertices `0, 1`. Each line must say `ok`.
-/

open R7 Tournament

def readMatrix (path : System.FilePath) : IO (Array (Array Nat)) := do
  let s ← IO.FS.readFile path
  let words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")
  let rows := (s.splitOn "\n").filter (fun l => !(words l).isEmpty)
  return rows.toArray.map fun l => (words l).toArray.map fun w => w.toNat?.getD 2

/-- Compare `T` with the `n × n` block of the matrix file starting at row/column `off`. -/
def checkBlock {n : ℕ} (name : String) (T : Tournament (Fin n)) [DecidableRel T.beats]
    (path : String) (off : ℕ := 0) (wholeFile : Bool := true) : IO Unit := do
  let M ← readMatrix ("../data/" ++ path)
  let mut bad : Nat := 0
  if wholeFile && M.size != n then
    IO.println s!"{name}: MISMATCH (file has {M.size} rows, expected {n})"
    return
  for i in List.finRange n do
    for j in List.finRange n do
      if i ≠ j then
        let e := (M[off + i.val]!)[off + j.val]!
        if (e == 1) != decide (T.beats i j) then bad := bad + 1
  IO.println s!"{name} vs data/{path} (offset {off}): {if bad == 0 then "ok" else s!"MISMATCH ({bad} entries)"}"

#eval do
  checkBlock "H6" H6 "H6.txt"
  checkBlock "W7" W7 "W7.txt"
  checkBlock "Y8" Y8 "Y8.txt"
  checkBlock "O21s" O21s "O21star.txt"
  checkBlock "ST27" ST27 "ST27.txt"
  checkBlock "ST26" ST26 "ST27.txt" 1 false
  checkBlock "ST25" ST25 "ST27.txt" 2 false
  checkBlock "ST26" ST26 "ST26-p-TT5.txt" 0 false
  checkBlock "TT 5" (TT 5) "ST26-p-TT5.txt" 27 false
  checkBlock "I24A" I24A "I24_A.txt"
  checkBlock "I24B" I24B "I24_B.txt"
  checkBlock "I24C" I24C "I24_C.txt"
  checkBlock "I24D" I24D "I24_D.txt"
  checkBlock "I24E" I24E "I24_E.txt"
  checkBlock "I23A" I23A "I23_A.txt"
  checkBlock "I23B" I23B "I23_B.txt"
  checkBlock "I23C" I23C "I23_C.txt"
  checkBlock "I23D" I23D "I23_D.txt"
  checkBlock "I23E" I23E "I23_E.txt"
  checkBlock "I23F" I23F "I23_F.txt"
  checkBlock "I23G" I23G "I23_G.txt"
  checkBlock "I23H" I23H "I23_H.txt"
  checkBlock "I23I" I23I "I23_I.txt"
  checkBlock "I23J" I23J "I23_J.txt"
  checkBlock "I23K" I23K "I23_K.txt"
  checkBlock "I23L" I23L "I23_L.txt"
  checkBlock "I23M" I23M "I23_M.txt"
  checkBlock "I23N" I23N "I23_N.txt"
  checkBlock "I23O" I23O "I23_O.txt"
  checkBlock "I23P" I23P "I23_P.txt"
  checkBlock "I23Q" I23Q "I23_Q.txt"
  checkBlock "I23R" I23R "I23_R.txt"
  checkBlock "I23S" I23S "I23_S.txt"
  checkBlock "I23T" I23T "I23_T.txt"
  checkBlock "I23U" I23U "I23_U.txt"
  checkBlock "I23V" I23V "I23_V.txt"
  checkBlock "I23W" I23W "I23_W.txt"
  checkBlock "I23X" I23X "I23_X.txt"
  checkBlock "I23Y" I23Y "I23_Y.txt"

/-! The indexed families list the letters in order. -/

example : I24 = ![I24A, I24B, I24C, I24D, I24E] := rfl
example : I23 0 = I23A ∧ I23 23 = I23X ∧ I23 24 = I23Y := ⟨rfl, rfl, rfl⟩
