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
      simp[←contra, (fwf c cmem).1.2.2] at unit_name_mem
    simp[propogate, List.nodup_cons, Trail.names_cons, twf, ALit.name, unit_ud, this]
  case right =>
    intro n nmem
    simp[propogate] at nmem
    cases nmem
    case head =>
      have := Formula.mem_memClause_mem_names cmem unit_name_mem
      simp[ALit.name, this]
    case tail mem => exact twf.2 n mem

theorem ppg_negation_con {l : Lit} {t : Trail}{c : Clause}{cu : c.unit t}{f : Formula}:
  propogate t c cu = ALit.deduced l :: t → c ∈ f → ALit.decided l.negate :: t ⊭ f := by
  intro h hmem
  simp[propogate] at h
  have lmem : l ∈ c := by
    rw[←h]
    exact Clause.unit_mem
  have lud : t ¿ l := by
    rw[←h]
    exact Clause.unit_ud
  simp[Clause.unit] at cu
  obtain ⟨ k, kmem, kud, kall ⟩ := cu
  by_cases heq : l = k
  case neg =>
    have := kall l lmem heq
    simp[Conflict.con, Undecided.ud] at lud this
    have := Trail.mem_lits_mem_names this
    simp[Lit.name_name_negate] at this
    contradiction
  case pos =>
    simp[Conflict.con] at kall ⊢
    exists c
    simp[hmem]
    intro j jmem
    by_cases heq2 : j = k
    case pos =>
      rw[heq2, heq]
      simp[Trail.lits, ALit.lit]
    case neg =>
      have := kall j jmem heq2
      simp[Trail.lits_cons, this]

theorem ppg_deduction_inv {t : Trail}{c : Clause}{cu : c.unit t}{f : Formula}:
  t.deduction_wf f → c ∈ f → Trail.deduction_wf f (propogate t c cu) := by
  intro h cmem
  let l := c.getunit t cu
  have : propogate t c cu = ALit.deduced l :: t := by
    simp[propogate, l]
  rw[this]
  simp[Trail.deduction_wf]
  have := ppg_negation_con this cmem
  constructor
  case left =>
    intro hd
    left
    exact (Trail.con_cons_con this) hd
  case right =>
    exact h
