import SATsolver.Experiment.Relations.Satisfies
import SATsolver.Experiment.Relations.Conflicts
import SATsolver.Experiment.Relations.Undecided

theorem Clause.ud_exUnseen{c : Clause}{t : Trail}:
  t¿c → ∃ l ∈ c, t.unseen l.name := by
  simp[Undecided.ud]
  intro l lmem lunseen cud
  exists l

theorem Formula.ud_exCUd{f : Formula}{t : Trail}:
  t¿f → f ≠ [] := by
  cases f
  all_goals simp[Undecided.ud]

theorem Formula.Clause.ud_exUnseen{f : Formula}{t : Trail}:
  t¿f → ∃ n ∈ f.names, t.unseen n := by
  simp [Undecided.ud, Formula.names]
  intro c cmem l lmem lunseen ohters
  have cn : l.name ∈ c.names := Clause.mem_mem_name lmem
  have fn : l.name ∈ f.names := Formula.mem_memClause_mem_names cmem cn
  exists l.name
  constructor
  case left => exists c
  case right =>  simp[Trail.unseen, lunseen]

theorem Clause.nSatCon_ud{c : Clause}{t : Trail}:
   ¬ t ⊭ c → ¬t ⊨ c → t¿c := by
  simp[Satisfies.sat, Conflict.con, Undecided.ud]
  intro l lmem lncon nsat
  have lnsat := nsat l lmem
  constructor
  case left =>
    exists l
    constructor
    case left => exact lmem
    case right =>
      intro contra
      obtain ⟨ a, amem, aname ⟩ := Trail.mem_name_exists_mem contra
      rw[←ALit.name_name_lit] at aname
      have litmem := Trail.mem_mem_lits amem
      cases Lit.shared_name aname
      case inl heq => rw[heq] at litmem; contradiction
      case inr heq => rw[heq] at litmem; contradiction
  case right =>
    intro k kmem
    have := nsat k kmem
    by_cases kcon : k.negate ∈ t.lits
    case pos => simp[kcon]
    case neg =>
      left
      intro contra
      obtain ⟨ a, amem, aname ⟩ := Trail.mem_name_exists_mem contra
      rw[←ALit.name_name_lit] at aname
      have litmem := Trail.mem_mem_lits amem
      cases Lit.shared_name aname
      case inl heq => rw[heq] at litmem; contradiction
      case inr heq => rw[heq] at litmem; contradiction


theorem Formula.nSatCon_ud{f : Formula}{t : Trail}:
  ¬t ⊨ f → ¬ t ⊭ f → t¿f := by
  simp[Formula.sat_iff_all_csSat, Formula.con_iff_exists_csCon, Formula.ud_iff_exists_csUD]
  intro c cmem ncSat ncon
  have ncCon := ncon c cmem
  have := Clause.nSatCon_ud ncCon ncSat
  exists c
