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


theorem length_le_of_nodup_all_le {l : List Nat}{n : Nat}:
  l.Nodup → 0 ∉ l → (∀ m ∈ l, m ≤ n) → l.length ≤ n := by
  intro nodup hzero hall
  induction n generalizing l
  case zero =>
    simp
    false_or_by_contra
    rename _ => contra
    obtain ⟨ n, ns, hn ⟩ := List.ne_nil_iff_exists_cons.mp contra
    subst hn
    have : n = 0 := by
      have := hall n (by simp)
      simp[←Nat.le_zero, this]
    simp[this] at hzero
  case succ x ih =>
    let l' := l.erase (x+1)
    have nodup' : l'.Nodup := List.Nodup.erase (x+1) nodup
    have hzero' : 0 ∉ l' := by
      intro contra
      have := List.mem_of_mem_erase contra
      contradiction
    have hall' : ∀ (m : Nat), m ∈ l' → m ≤ x := by
      intro y ymem
      have : y ∈ l := List.mem_of_mem_erase ymem
      have : y ≤ x + 1 := hall y this
      simp[l', List.Nodup.mem_erase_iff nodup] at ymem
      simp[Nat.le_iff_lt_or_eq, ymem.1] at this
      exact Nat.le_iff_lt_add_one.mpr this
    have ihc := ih nodup' hzero' hall'
    by_cases hmem : (x+1) ∈ l
    case pos =>
      have : l'.length = l.length - 1 := List.length_erase_of_mem hmem
      simp[this] at ihc
      exact ihc
    case neg =>
      have : l' = l := List.erase_of_not_mem hmem
      simp[←this, Nat.le_succ_of_le, ihc]

theorem length_eq_of_nodup_complete_le {l : List Nat}{n : Nat}:
  l.Nodup → 0 ∉ l → (∀ m ∈ l, m ≤ n) → (∀ m ≤ n, m ∈ l) → l.length = n := by
  intro nodup hzero hall complete
  induction n generalizing l
  case zero =>
    cases l
    case nil => simp
    case cons hd tl =>
      have : hd ≤ 0 := hall hd (by simp)
      have : hd = 0 := Nat.le_zero.mp this
      subst this
      simp at hzero
  case succ n ih =>
    let l' := l.erase (n+1)
    have nodup' : l'.Nodup := List.Nodup.erase (n+1) nodup
    have hzero' : 0 ∉ l' := by
      intro contra
      have := List.mem_of_mem_erase contra
      contradiction
    have hall' : ∀ (m : Nat), m ∈ l' → m ≤ n := by
      intro y ymem
      have : y ∈ l := List.mem_of_mem_erase ymem
      have : y ≤ n + 1 := hall y this
      simp[l', List.Nodup.mem_erase_iff nodup] at ymem
      simp[Nat.le_iff_lt_or_eq, ymem.1] at this
      exact Nat.le_iff_lt_add_one.mpr this
    have complete' : ∀ (m : Nat), m ≤ n → m ∈ l' := by
      intro x hmem
      simp[l', List.Nodup.mem_erase_iff nodup]
      have := Nat.le_succ_of_le hmem
      simp[complete x this]
      intro contra
      simp[contra] at hmem
      simp +arith at hmem
    have ihc := ih nodup' hzero' hall' complete'
    have hmem : (n+1) ∈ l := complete (n+1) (by simp)
    have : l'.length = l.length - 1 := List.length_erase_of_mem hmem
    simp[this] at ihc
    have : 1 ≤ l.length := by
      false_or_by_contra
      rename _ => contra
      have := Nat.gt_of_not_le contra
      simp at this
      simp[this] at hmem
    simp[← ihc, Nat.sub_add_cancel this]

theorem length_lt_of_nodup_incomplete_le {l : List Nat}{n : Nat}:
  n ≠ 0 → l.Nodup → 0 ∉ l → (∃ e ≤ n, 0 < e ∧ e ∉ l)→ (∀ m ∈ l, m ≤ n) → l.length < n := by
  intro neq nodup hzero incopmlete hall
  induction n generalizing l
  case zero => contradiction
  case succ n ih =>
    let l' := l.erase (n+1)
    have nodup' : l'.Nodup := List.Nodup.erase (n+1) nodup
    have hzero' : 0 ∉ l' := by
      intro contra
      have := List.mem_of_mem_erase contra
      contradiction
    have hall' : ∀ (m : Nat), m ∈ l' → m ≤ n := by
      intro y ymem
      have : y ∈ l := List.mem_of_mem_erase ymem
      have : y ≤ n + 1 := hall y this
      simp[l', List.Nodup.mem_erase_iff nodup] at ymem
      simp[Nat.le_iff_lt_or_eq, ymem.1] at this
      exact Nat.le_iff_lt_add_one.mpr this
    obtain ⟨ e, hle, h0lt, emem ⟩ := incopmlete
    cases Nat.lt_or_eq_of_le hle
    case inl hlt =>
      have incomplete' : ∃ e, e ≤ n ∧ 0 < e ∧ ¬e ∈ l' := by
        exists e
        have : e ≠ n + 1 := Nat.ne_of_lt hlt
        rw[←List.mem_erase_of_ne this] at emem
        simp[l', emem, Nat.le_of_lt_add_one, hlt, h0lt]
      by_cases heq : n = 0
      case pos =>
        subst heq
        simp at hlt
        simp[hlt] at h0lt
      case neg =>
        have ihc := ih heq nodup' hzero' incomplete' hall'
        by_cases hmem : (n+1) ∈ l
        case pos =>
          have : l'.length = l.length - 1 := List.length_erase_of_mem hmem
          rw[this] at ihc
          have : 1 ≤ l.length := by
            false_or_by_contra
            rename _ => contra
            have := Nat.gt_of_not_le contra
            simp at this
            simp[this] at hmem
          have := Nat.le_of_lt ihc
          simp at this
          cases Nat.lt_or_eq_of_le this
          case inl this => exact this
          case inr this => simp[this] at ihc
        case neg =>
          have : l' = l := List.erase_of_not_mem hmem
          simp[←this, Nat.lt_succ_of_lt, ihc]
    case inr heq =>
      rw[heq] at emem
      have heq : l' = l := List.erase_of_not_mem emem
      have := length_le_of_nodup_all_le nodup' hzero' hall'
      rw[heq] at this
      simp[Nat.lt_succ_iff, this]

theorem Variables.ud_not_nil{v : Variables}{t : Trail}{f : Formula}:
  f.wf → v.wf f → t ¿ f → v ≠ 0 := by
  simp[Formula.wf, Clause.wf,  Variables.wf, Undecided.ud]
  intro hall vwf₁ vwf₂ c cmem l lmem lud cud
  have lcn : l.name ∈ c.names := Clause.mem_mem_name lmem
  have lfn : l.name ∈ f.names := by
    exact Formula.mem_memClause_mem_names cmem lcn
  have vge : l.name ≤ v := vwf₁ l.name lfn
  have : 0 < l.name := by
    have := (hall c cmem).2.2
    by_cases heq : l.name =0
    case pos => rw[heq] at lcn; contradiction
    case neg => simp[←Nat.ne_zero_iff_zero_lt, heq]
  have : 0 < v := Nat.lt_of_lt_of_le this vge
  simp[Nat.ne_zero_iff_zero_lt, this]


theorem Trail.ud_vars{t : Trail}{f : Formula}{v : Variables} :
  t.wf → f.wf → v.wf f → (∀ n ∈ t.names, n ∈ f.names) → t ¿ f → t.names.length < v := by
  intro twf fwf vwf htf fud
  have v_ne_zero := Variables.ud_not_nil fwf vwf fud
  simp[Trail.wf, Formula.wf, Variables.wf, Undecided.ud] at *
  have h1 : ∀ n ∈ t.names, n ≤ v := by
    intro n nmem
    have : n ∈ f.names := htf n nmem
    exact vwf.1 n this
  have h2 : ∃ e, e ≤ v ∧ 0 < e ∧ ¬e ∈ t.names := by
    obtain ⟨ c, cmem, cud ⟩ := fud
    obtain ⟨ l, lmem, lud ⟩ :=cud.1
    exists l.name
    simp[lud]
    have cwf : c.wf := fwf c cmem
    simp[Clause.wf] at cwf
    by_cases heq : l.name =0
    case pos =>
      have := Clause.mem_mem_name lmem
      simp[heq, cwf] at this
    case neg =>
      simp[←Nat.ne_zero_iff_zero_lt, heq]
      apply vwf.1
      have := Clause.mem_mem_name lmem
      exact Formula.mem_memClause_mem_names cmem this
  exact length_lt_of_nodup_incomplete_le v_ne_zero twf.1 twf.2 h2 h1


theorem Trail.mem_vwf {t : Trail}{v : Variables}{f :Formula}:
  t.wf → (∀ (n : Nat), n ∈ t.names → n ∈ f.names) → v.wf f → t.length ≤ v := by
  intro twf htf vwf
  simp[Variables.wf, Trail.wf] at vwf twf
  have : ∀ (n : Nat), n ∈ t.names → n ≤ v := by
    intro n nmem
    have := htf n nmem
    exact vwf.1 n this
  have := length_le_of_nodup_all_le twf.1 twf.2 this
  simp[names] at this
  exact this
