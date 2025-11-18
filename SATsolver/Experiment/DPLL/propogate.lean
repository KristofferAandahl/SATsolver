import SATsolver.Experiment.Relations.Theories

def propogate (t : Trail)(c : Clause)(wf : c.unit t): Trail :=
  let l := c.getunit t wf
  ALit.deduced l :: t

theorem ppg_preserves_wf {t : Trail}{c : Clause}{cu : c.unit t}{f : Formula}
  {fwf : f.wf}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}:
  c ∈ f → (propogate t c cu).wf ∧ ∀ n ∈ (propogate t c cu).names, n ∈ f.names := by
  intro cmem
  have unit_ud : t ¿ c.getunit t cu := Clause.unit_ud
  have unit_mem : c.getunit t cu ∈ c := Clause.unit_mem
  have unit_name_mem := Clause.mem_mem_name unit_mem
  simp[Trail.wf, Undecided.ud, Formula.wf, Clause.wf] at *
  constructor
  case left =>
    have : 0 ≠ (c.getunit t cu).name := by
      intro contra
      simp[←contra, (fwf c cmem).2.2] at unit_name_mem
    simp[propogate, List.nodup_cons, Trail.names_cons, twf, ALit.name, unit_ud, this]
  case right =>
    intro n nmem
    simp[propogate] at nmem
    cases nmem
    case head =>
      have := Formula.mem_memClause_mem_names cmem unit_name_mem
      simp[ALit.name, this]
    case tail mem => exact twf.2 n mem
