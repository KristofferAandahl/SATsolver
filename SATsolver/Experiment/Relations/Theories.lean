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

theorem Trail.nil_ud{f : Formula}:
  f ≠ [] → f.wf → ([] : Trail) ¿ f := by
  intro h wf
  obtain ⟨ c, tl, heq ⟩ := List.ne_nil_iff_exists_cons.mp h
  subst heq
  simp[Undecided.ud, Formula.wf, Clause.wf] at wf ⊢
  have : c ≠ [] := wf.1.1.1
  obtain ⟨ l, ls, heq ⟩ := List.ne_nil_iff_exists_cons.mp this
  subst heq
  left
  constructor
  case left =>
    exists l
    simp[Trail.names]
  case right =>
    intro k kmem
    simp[Trail.names]


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
    have := (hall c cmem).1.2.2
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
    have cwf : c.wf := (fwf c cmem).1
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

theorem Trail.con_cons_con{tl : Trail}{f : Formula}:
  tl ⊭ f → ∀ hd, (hd ++ tl) ⊭ f := by
  simp[Conflict.con, Trail.lits]
  intro c cmem call hd
  exists c
  simp[cmem]
  intro l lmem
  have := call l lmem
  simp[this]


theorem Trail.con_tl_con_or_ud {f : Formula}{hd : ALit}{tl : Trail}:
  Trail.wf (hd::tl) → hd::tl ⊭ f → tl ⊭ f ∨ tl ¿ f := by
  intro twf h
  simp[Conflict.con, Undecided.ud] at h ⊢
  obtain ⟨ c, cmem,  call ⟩ := h
  simp[←exists_or]
  exists c
  simp[cmem]
  by_cases h : (∀ (l : Lit), l ∈ c → l.negate ∈ tl.lits)
  case pos => left; exact h
  case neg =>
    right
    simp at h
    obtain ⟨ x, xmem ,xh ⟩ := h
    have := call x xmem
    simp[Trail.lits_cons, xh] at this
    constructor
    case left =>
      exists x
      have := congrArg Lit.name this
      simp[Lit.name_name_negate, ALit.name_name_lit] at this
      have twfhd := Trail.wf_hd twf
      simp[xmem, this, twfhd]
    case right =>
      intro l lmem
      have := call l lmem
      simp[Trail.lits_cons] at this
      cases this
      case inl lh =>
        have := congrArg Lit.name lh
        simp[Lit.name_name_negate, ALit.name_name_lit] at this
        have twfhd := Trail.wf_hd twf
        simp[this, twfhd]
      case inr rh => right; exact rh

theorem Trail.ud_tl_ud {f : Formula}{hd : ALit}{tl : Trail}:
  Trail.wf (hd::tl) → (hd::tl) ¿ f → tl ¿ f := by
  simp[Undecided.ud, Trail.wf]
  intro nodup nzero c cmem l lmem hname hall
  exists c
  simp[cmem]
  constructor
  case left =>
    exists l
    constructor
    exact lmem
    simp[Trail.names_cons] at hname
    simp[hname]
  case right =>
    intro l lmem
    have := hall l lmem
    simp[Trail.names_cons] at this
    cases this
    case inl h => left; simp[h]
    case inr h =>
      simp[Conflict.con] at h ⊢
      simp[Trail.lits_cons] at h
      cases h
      case inl h =>
        have := congrArg Lit.name h
        simp[Lit.name_name_negate] at this
        left
        rw[this]
        simp[Trail.names, List.nodup_cons] at nodup
        simp[Trail.names, ALit.name_name_lit]
        exact nodup.1
      case inr h =>
        right; exact h

theorem forall_and_right {α} {p: Prop}{q : α → Prop} :
  (∃ (_ : α), True) → ((∀ (x : α), p ∧ q x) ↔ p ∧ ∀ (x : α), q x) := by
  intro exi
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      obtain ⟨ a ⟩ := exi
      exact (h a).1
    case right =>
      intro a
      exact (h a).2
  case mpr =>
    intro h x
    constructor
    case left => exact h.1
    case right => exact h.2 x

theorem for_all_or {α}{p q : α → Prop} :
  (∀ α, p α) ∨ (∀ α, q α) → (∀ α, p α ∨ q α)  := by
    intro h
    intro a
    cases h
    case inl lh => simp[lh a]
    case inr rh => simp[rh a]




theorem Trail.cons_con {f : Formula}{hd : ALit}{tl : Trail}:
  Trail.wf (hd::tl) → f.wf → (hd::tl) ⊭ f → tl ⊭ f ∨  tl ¿ f := by
  intro twf wf h
  simp[Conflict.con, Undecided.ud] at h ⊢
  obtain ⟨ c, cmem, call ⟩ := h
  simp[←exists_or]
  exists c
  simp[cmem]
  have hname : hd.name ∉ tl.names := by
    have := twf.1
    simp[Trail.names] at this ⊢
    exact this.1
  by_cases hdmem : hd.lit.negate ∈ c
  case pos =>
    right
    constructor
    case left =>
      exists hd.lit.negate
      simp[Lit.name_name_negate, ALit.name_name_lit, hname, hdmem]
    case right =>
      intro l lmem
      have := call l lmem
      simp[Trail.lits] at this ⊢
      cases this
      case inl h =>
        have := congrArg Lit.name h
        simp[Lit.name_name_negate, ALit.name_name_lit] at this
        simp[this, hname]
      case inr h => simp[h]
  case neg =>
    left
    intro l lmem
    have := call l lmem
    simp[Trail.lits] at this ⊢
    cases this
    case inl h =>
        have := congrArg Lit.negate h
        simp[Lit.negneg] at this
        rw[this] at lmem
        contradiction
    case inr h => exact h

theorem Trail.ud_append {f : Formula}{hd tl : Trail}:
  Trail.wf (hd ++ tl) → (hd ++ tl) ¿ f → hd ¿ f ∧ tl ¿ f := by
  intro twf hud
  simp[Undecided.ud] at hud ⊢
  obtain ⟨ c, cmem, lh, call ⟩ := hud
  obtain ⟨ l, lmem, lname ⟩ := lh
  constructor
  case left =>
    exists c
    constructor
    case left => exact cmem
    case right =>
      constructor
      case left =>
        exists l
        constructor
        case left => exact lmem
        case right =>
          simp [Trail.names] at lname ⊢
          intro a amem
          exact lname.1 a amem
      case right =>
        intro l lmem
        have := call l lmem
        simp [Conflict.con] at this ⊢
        cases this
        case inl lh => left; simp[Trail.names] at lh ⊢; exact lh.1
        case inr rh =>
          simp[Trail.lits] at rh ⊢
          cases rh
          case inl lh => right; exact lh
          case inr rh =>
            left
            simp[Trail.wf, Trail.names, List.nodup_append] at twf
            have : l.negate ∈ tl.lits := by
              simp[Trail.lits]; exact rh
            have : l.negate.name ∈ tl.names := Trail.mem_lits_mem_names this
            rw[Lit.name_name_negate] at this
            simp[Trail.names] at this ⊢
            obtain ⟨ a, amem, heq ⟩ := this
            intro a1 a1mem
            have := twf.1.2.2 a1 a1mem a amem
            rw[heq] at this
            exact this
  case right =>
    exists c
    constructor
    case left => exact cmem
    case right =>
      constructor
      case left =>
        exists l
        constructor
        case left => exact lmem
        case right =>
          simp [Trail.names] at lname ⊢
          intro a amem
          exact lname.2 a amem
      case right =>
        intro l lmem
        have := call l lmem
        simp [Conflict.con] at this ⊢
        cases this
        case inl lh => left; simp[Trail.names] at lh ⊢; exact lh.2
        case inr rh =>
          simp[Trail.lits] at rh ⊢
          cases rh
          case inr rh => right; exact rh
          case inl lh =>
            left
            simp[Trail.wf, Trail.names, List.nodup_append] at twf
            have : l.negate ∈ hd.lits := by
              simp[Trail.lits]; exact lh
            have : l.negate.name ∈ hd.names := Trail.mem_lits_mem_names this
            rw[Lit.name_name_negate] at this
            simp[Trail.names] at this ⊢
            obtain ⟨ a, amem, heq ⟩ := this
            intro a1 a1mem
            have := twf.1.2.2 a amem a1 a1mem
            rw[heq] at this
            intro contra
            apply this
            symm
            exact contra

def Trail.deduction_wf (f : Formula) : Trail → Prop
  | [] => True
  | ALit.deduced l :: tl => (∀ (hd : Trail), Trail.wf (hd ++ tl) → l.negate ∈ hd.lits →
      (hd ++ tl ⊭ f) ∨ (hd ++ tl) ¿ f) ∧
    Trail.deduction_wf f tl
  | ALit.decided _ :: tl => Trail.deduction_wf f tl

theorem Trail.dedwf_cons :
  Trail.deduction_wf f (a::tl) → Trail.deduction_wf f tl := by
  intro h
  cases a
  case decided => simpa [Trail.deduction_wf] using h
  case deduced => exact h.2

theorem Trail.dedwf_append :
  Trail.deduction_wf f (hd++tl) → Trail.deduction_wf f tl := by
  intro h
  induction hd
  case nil => simpa using h
  case cons hd1 hd2 ih =>
    exact ih (Trail.dedwf_cons h)

theorem Trail.lit_type_ag_con {l : Lit}{tl : Trail}{f : Formula}:
  ALit.decided l ::tl ⊭ f ↔ ALit.deduced l ::tl ⊭ f := by
  simp[Conflict.con]
  constructor
  all_goals
  intro h
  obtain ⟨ c, ch ⟩ := h
  exists c

theorem Trail.lit_type_ag_ud {l : Lit}{tl : Trail}{f : Formula}:
  ALit.decided l ::tl ¿  f ↔ ALit.deduced l ::tl ¿ f := by
  simp[Undecided.ud]
  constructor
  all_goals
  intro h
  obtain ⟨ c, ch ⟩ := h
  exists c

theorem Trail.no_sat {hd : ALit}{tl : Trail}{f : Formula}:
  Trail.wf (hd::tl) → hd::tl ⊭ f ∧ hd.negate::tl ⊭ f → ∀ hd, Trail.wf (hd++tl) → hd ++ tl ⊭ f ∨ hd ++ tl ¿ f := by
  intro twf h hd' twf'
  simp[Conflict.con, Undecided.ud] at h ⊢
  obtain ⟨ h1, h2 ⟩ := h
  obtain ⟨ c1, c1mem, c1hd ⟩ := h1
  obtain ⟨ c2, c2mem, c2hdn ⟩ := h2
  by_cases hmem : hd.lit ∈ hd'.lits
  case pos =>
    left
    exists c1
    constructor
    case left => exact c1mem
    case right =>
      intro l lmem
      have := c1hd l lmem
      simp[Trail.lits] at this hmem ⊢
      cases this
      case inl lh => left; rw[lh]; simp[hmem]
      case inr rh => right; exact rh
  case neg =>
    by_cases hnmem : hd.negate.lit ∈ hd'.lits
    case pos =>
      left
      exists c2
      constructor
      case left => exact c2mem
      case right =>
        intro l lmem
        have := c2hdn l lmem
        simp[Trail.lits] at this hnmem ⊢
        cases this
        case inl lh => left; rw[lh]; simp[hnmem]
        case inr rh => right; exact rh
    case neg =>
      by_cases hdc2 : hd.lit ∈ c2
      case pos =>
        right
        exists c2
        constructor
        case left => exact c2mem
        case right =>
          constructor
          case left =>
            exists hd.lit
            simp[hdc2, ALit.name_name_lit]
            rw[←ALit.name_name_lit, ←Trail.mem_lits_names_eq]
            simp
            have := Trail.wf_hd twf
            constructor
            case left =>
              have : ¬hd.lit ∈ tl.lits := by
                intro contra
                have := Trail.mem_lits_mem_names contra
                simp[ALit.name_name_lit] at this
                contradiction
              simp[Trail.lits_append, hmem, this]
            case right =>
              have : ¬hd.lit.negate ∈ tl.lits := by
                intro contra
                have := Trail.mem_lits_mem_names contra
                simp[Lit.name_name_negate, ALit.name_name_lit] at this
                contradiction
              simp[Trail.lits_append, this]
              simp[←ALit.lit_negate_negate_lit, hnmem]
          case right =>
            intro l lmem
            have hnmem := Trail.mem_lits_mem_names (c2hdn l lmem)
            have := Trail.names_cons hd.negate tl
            simp[this] at hnmem
            simp[Lit.name_name_negate, ALit.name_name_negate] at hnmem
            cases hnmem
            case inl lh =>
              left
              simp[Trail.names_append, lh]
              have := Trail.wf_hd twf
              simp[this]
              simp[←ALit.name_name_lit, ←Trail.mem_lits_names_eq]
              simp[hmem, ←ALit.lit_negate_negate_lit, hnmem]
            case inr rh =>
              have lnegmem := c2hdn l lmem
              simp[Trail.lits_cons] at lnegmem
              have : ¬ l.negate = hd.negate.lit := by
                intro contra
                have := congrArg Lit.negate contra
                simp[Lit.negneg] at this
                rw[this] at rh
                simp[Lit.name_name_negate, ALit.name_name_lit, ALit.name_name_negate] at rh
                have := Trail.wf_hd twf
                contradiction
              simp[this] at lnegmem
              right
              simp[Trail.lits_append]
              right
              exact lnegmem
      case neg =>
        have : ∀ (l : Lit), l ∈ c2 → l.negate ∈ lits tl := by
          intro l lmem
          have := c2hdn l lmem
          simp[Trail.lits_cons] at this
          cases this
          case inl lh =>
            have lh := congrArg Lit.negate lh
            simp[ALit.lit_negate_negate_lit , Lit.negneg] at lh
            rw[lh] at lmem
            contradiction
          case inr rh =>
            exact rh
        left
        exists c2
        simp[c2mem]
        intro l lmem
        simp[Trail.lits_append]
        right
        exact this l lmem


theorem con_or_ud {t : Trail}{f : Formula} :
  t ⊭ f ∨ t ¿ f ↔ ∃ c ∈ f, ∀ l ∈ c, l.negate ∈ t.lits ∨ l.name ∉ t.names := by
  constructor
  case mp =>
    intro h
    simp[Conflict.con, Undecided.ud] at h
    rw[←exists_or] at h
    obtain ⟨ c, ch⟩ := h
    cases ch
    case inl ch =>
      exists c
      simp[ch.1]
      intro l lmem
      simp[ ch.2 l lmem]
    case inr ch =>
      exists c
      simp[ch.1]
      intro l lmem
      have := ch.2.2 l lmem
      rw[or_comm]
      simp[this]
  case mpr =>
    intro h
    obtain ⟨ c, cmem, ch ⟩ := h
    simp[Conflict.con, Undecided.ud, ← exists_or]
    exists c
    simp[cmem]
    by_cases ud : (∃ l', l' ∈ c ∧ ¬l'.name ∈ t.names)
    case pos =>
      right
      simp[ud]
      intro l lmem
      have := ch l lmem
      rw[or_comm]
      simp[this]
    case neg =>
      simp at ud
      left
      intro l lmem
      have namemem := ud l lmem
      have := ch l lmem
      simp[namemem] at this
      exact this


theorem mem_sat {t : Trail}{a : ALit}{f : Formula}:
  a ∈ t → (t ⊨ f ↔ a::t ⊨ f) := by
  intro amem
  simp[Satisfies.sat]
  constructor
  case mp =>
    intro h c cmem
    obtain ⟨  l, lc, lt ⟩ := h c cmem
    exists l
    constructor
    case left => exact lc
    case right =>
      simp[Trail.lits] at lt ⊢
      right; exact lt
  case mpr =>
    intro h c cmem
    obtain ⟨ l, lc, lt ⟩ := h c cmem
    exists l
    constructor
    case left => exact lc
    case right =>
      simp[Trail.lits] at lt ⊢
      cases lt
      case inl lh => exists a; simp[amem, lh]
      case inr rh => exact rh

theorem extract_mem {α} {l : List α}{a : α}:
  a ∈ l → ∃ (k : List α), a ∉ k → ∀ (b : α), b ≠ a → (b ∈ l ↔ b ∈ k) := by
  intro mem
  induction l
  case nil => simp at mem
  case cons x xs ih =>
    cases mem
    case head =>
      exists xs
      intro nmem b neq
      simp[neq]
    case tail hmem =>
      have := ih hmem
      obtain ⟨ k, kh⟩ := this
      exists x::k
      intro nmem b heq
      have : a ∉ k := by
        intro contra
        apply nmem
        simp[contra]
      have := kh this b heq
      simp[this]

/-
theorem wf_erase {hd tl : Trail}{a : ALit}:
  a ∈ hd → (hd++tl).wf → Trail.wf (a::tl) →  Trail.wf ((hd.erase a)++a::tl) := by
  intro amem wf_app wf_con
  simp[Trail.wf] at *
  constructor
  case right =>
    simp[Trail.names]
    constructor
    case left =>
      intro b bmem
      have bhd := List.mem_of_mem_erase bmem
      have := wf_app.2
      simp[Trail.names] at this
      exact this.1 b bhd
    case right =>
      have := wf_con.2
      simp[Trail.names] at this
      exact this
  case left =>
    simp[Trail.names, List.nodup_append]
    constructor
    case left =>
      have := wf_app.1
      simp[Trail.names, List.nodup_append] at this
      have nodup := this.1
      have hsub : (List.erase hd a).Sublist hd := List.erase_sublist
      have : (List.map ALit.name (List.erase hd a)).Sublist (List.map ALit.name hd) := by
        rw[List.sublist_map_iff]
        exists hd.erase a
      exact List.Nodup.sublist this nodup
    case right =>
      constructor
      case left =>
        have := wf_con.1
        simp[Trail.names, List.nodup_cons] at this
        exact this
      case right =>
        intro b bmem
        have bmem := List.mem_of_mem_erase bmem
        constructor
        case left =>
          have := wf_app.1
          simp[Trail.names, List.nodup_append] at this
          have : hd.Nodup := by
            have := List.
          have := List.Nodup.not_mem_erase
          have := this.1
          simp[List.nodup_] at thi




theorem non_deduced {t : Trail}{f : Formula} :
  t.wf → (∀ a ∈ t, a.deducedP) → Trail.deduction_wf f t → ∀ t', (∃ l ∈ Trail.lits t', l.negate ∈ t.lits) → t' ⊭ f ∨ t' ¿ f:= by
  intro twf allded wf t' lh
  obtain ⟨ l, lmem, lneg ⟩ := lh
  simp[Trail.lits] at lneg
  obtain ⟨ a, amem, heq ⟩ := lneg
  induction t
  case nil => simp at amem
  case cons x xs ih =>
    simp at amem
    cases amem
    case inl lh =>
      subst lh
      cases a
      case decided k =>
        have := allded (ALit.decided k) (by simp)
        simp[ALit.deducedP] at this
      case deduced k =>
        simp[Trail.deduction_wf] at wf
        have := wf.1 [] twf
        simp at this
-/
