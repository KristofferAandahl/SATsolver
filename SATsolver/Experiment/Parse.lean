import SATsolver.Experiment.Data.Formula

open IO

def parseClause (line : String) : Clause :=
  line.splitOn " "
  |>.foldl
      (fun acc tok =>
        if tok.isEmpty then acc
        else
          let i := String.toInt! tok
          if i == 0 then acc
          else
            let lit :=
              if i < 0 then
                Lit.neg (Int.natAbs i)
              else
                Lit.pos (Int.natAbs i)
            lit :: acc)
      []
  |> List.reverse

def readDimacs (fileName : System.FilePath) : IO (Nat × Formula) := do
  IO.FS.withFile fileName .read fun h => do
    let mut nVars : Nat := 0
    let mut clauses : Formula := []

    while true do
      let line ← h.getLine
      if line.isEmpty then
        break

      let line := line.trim
      if line.isEmpty ∨ line.startsWith "c" then
        continue

      if line.startsWith "p" then
        let parts := line.splitOn " " |>.filter (· ≠ "")
        if parts.length ≠ 4 then
          throw <| IO.userError "Invalid DIMACS header"
        nVars := parts[2]!.toNat!
      else if line.startsWith "%" then
        break
      else
        let clause := parseClause line
        if ¬ clause.isEmpty then
          clauses := clause :: clauses

    return (nVars, clauses.reverse)
