import SatProver.CNF

partial def readLines (filename : System.FilePath) : IO (List String) := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  let rec loop (lines : List String) : IO (List String) := do
    let line ← handle.getLine
    if line.isEmpty ∨ line.startsWith "%" then
      pure lines.reverse
    else if line.startsWith "c" then
      loop lines
    else
      let cleaned := line.trim
      loop (cleaned :: lines)
  loop []

def parseClause (line : String) : Clause :=
  (
    line.splitOn " "
    |>.filter (· ≠ "")
    |>.map (String.toInt!)
    |>.takeWhile (· ≠ 0)
  ).toArray

def parseDimacs (lines : List String) : Except String CNF := do
  let mut nVars: Nat := 0
  let mut nClauses: Nat := 0
  let mut clauses : Array Clause := #[]
  for line in lines do
    if line.startsWith "c" ∨ line.startsWith "%" then
      pure ()
    else if line.startsWith "p" then
      let vals := line.splitOn " "
      if vals.length ≠ 4 then
        throw "Invalid file. Header wrong length"
      else
        nVars := vals[2]!.toNat!
        nClauses := vals[3]!.toNat!
    else
      let clause := parseClause line
      if ¬clause.isEmpty then
        clauses := clauses ++ [parseClause line]
  return ⟨ nVars, nClauses, clauses ⟩

def readDimacs (fileName : System.FilePath) : IO CNF := do
  let lines ←  readLines fileName
  match parseDimacs lines with
    | .ok cnf => pure cnf
    | .error msg => throw <| IO.userError msg

def main : IO Unit := do
  let cnf ← readDimacs "test.cnf"
  IO.println cnf
