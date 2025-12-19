import SATsolver.Experiment.Relations.Theories
import SATsolver.Experiment.DPLL.completeness

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
    intro hd wf lmem
    left
    simp[Conflict.con] at this ⊢
    obtain ⟨ c, cmem, call ⟩ := this
    exists c
    constructor
    case left => exact cmem
    case right =>
      intro j jmem
      have := call j jmem
      simp[Trail.lits] at this ⊢
      cases this
      case inl lh =>
        simp[ALit.lit] at lh
        left
        have := Trail.mem_lits_exists_mem lmem
        simp[lh, this]
      case inr rh =>
        right; exact rh
  case right =>
    exact h


theorem ppg_completeness {t : Trail}{c : Clause}{cu : c.unit t}{f : Formula}:
  (t.wf ∧ ∀ n ∈ t.names, n ∈ f.names) → f.wf → Completenes.invariant t f → c ∈ f → Completenes.invariant (propogate t c cu)  f := by
  intro twf fwf h cmem
  have ppgwf := ppg_preserves_wf cmem (twf := twf) (fwf := fwf) (cu := cu)
  let l := c.getunit t cu
  have : propogate t c cu = ALit.deduced l :: t := by
    simp[propogate, l]
  rw[this] at ppgwf ⊢
  have := ppg_negation_con this cmem
  simp[Completenes.invariant]
  constructor
  case left =>
    intro hd hdwf hsat contra
    simp[Conflict.con, Satisfies.sat] at this hsat
    obtain ⟨ c, cmem, call ⟩ := this
    obtain ⟨ j, jc, jt ⟩ := hsat c cmem
    have :=  call j jc
    simp[Trail.lits] at this
    cases this
    case inl lh =>
      simp[ALit.lit] at lh
      have lh := congrArg Lit.negate lh
      simp[Lit.negneg] at lh
      subst lh
      simp[Trail.lits_append] at jt
      cases jt
      case inl lh =>
        have := Trail.lit_and_litn_not_wf lh contra
        have := (Trail.wf_append hdwf).1
        contradiction
      case inr rh =>
        have contra : l.negate ∈ (hd++t).lits := by
          simp[Trail.lits_append]
          left; exact contra
        have rh : l ∈ (hd++t).lits := by
          simp[Trail.lits_append]
          right; exact rh
        have := Trail.lit_and_litn_not_wf rh contra
        contradiction
    case inr rh =>
      obtain ⟨  a, amem, heq ⟩ := rh
      have := Trail.mem_mem_lits amem
      rw[heq] at this
      have : j.negate ∈ (hd++t).lits := by
        simp[Trail.lits_append]
        right; exact this
      have := Trail.lit_and_litn_not_wf jt this
      contradiction
