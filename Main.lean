import Init.System.IO

import SATsolver.Experiment.Parse
import SATsolver.Experiment.DPLL.impl

def dpll_file (file: System.FilePath) : IO Nat := do
  let (nvars, cnf) ← readDimacs file
  let decstart ← IO.monoMsNow
  if call : cnf.all (·.wf) then
    if vwf : decide (Variables.wf nvars cnf) then
    let decend ← IO.monoMsNow
    IO.println s!"Time used: {decend-decstart}ms"
      have wf : cnf.wf ∧ Variables.wf nvars cnf := by
        simp at call vwf
        have fwf := wf_check call vwf
        exact And.intro fwf vwf
      IO.println "start"
      let start ← IO.monoMsNow
      let (b, t) ← pure (DPLL_maxo cnf nvars wf)
      let stop ← IO.monoMsNow
      IO.println s!"Time used: {stop-start}ms. Result {b} and {t}"
      return (stop-start)
    else
    IO.println "Wrong amount of vars"
    return 0
  else
    IO.println s!"{List.mergeSort cnf.names}"
    IO.println "Illeagal formula"
    return 0


def main : IO Unit := do
  let dir  ← System.FilePath.readDir "flat100-239"
  let mut average := 0
  let mut max := 0
  let mut files := 0
  for entry in dir do
    let time ← dpll_file entry.path
    if time == 0 then
      IO.println "error has been found"
      break
    else if max < time then max := time
    average := time + average
    files := files + 1
    /-if files >= 10 then break-/
  IO.print s!"Files run : {files}, average time {average/files} and max time {max}"
