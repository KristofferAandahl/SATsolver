import SATsolver.Experiment.DPLL.impl

theorem internal_final_state{f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}:
  internal t f v vz wf twf com = (b, t') → t' ⊨ f ∨ b = false := by
  unfold internal
  split
  case isTrue hsat =>
    simp at hsat ⊢
    intro bh heq
    simp[←heq, hsat]
  case isFalse hsat =>
    split
    case isTrue hcon =>
      split
      case isTrue exDec =>
        intro h
        exact internal_final_state h
      case isFalse exDec =>
        simp
        intro bh th
        simp[bh]
    case isFalse hcon =>
      simp
      split
      case isTrue hunit =>
        intro h
        exact internal_final_state h
      case isFalse hunit =>
        intro h
        exact internal_final_state h
termination_by distance t v vz
decreasing_by
  have : t.length < v := by
    rename ¬decide (t⊨f) = true => sat
    rename ¬decide (t⊭f) = true => con
    simp at sat con
    have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
    simp[Trail.names] at this
    exact this
  exact distance_dec this
  have : t.length < v := by
    rename ¬decide (t⊨f) = true => sat
    rename ¬decide (t⊭f) = true => con
    simp at sat con
    have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
    simp[Trail.names] at this
    exact this
  exact distance_prop this
  have : t.length ≤ v := Trail.mem_vwf twf.1 twf.2 wf.2
  exact distance_bc this

theorem DPLL.final_state{f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail}:
DPLL f  v wf = (b, t) → t ⊨ f ∨ b = false := by
  simp[DPLL]
  cases f
  case nil => simp[Satisfies.sat]
  case cons c cs =>
    simp
    exact internal_final_state

theorem internal_all_deduced_if_con{f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}:
  internal t f v vz wf twf com = (b, t') → b = false → (t' ⊭ f ∧  ∀ a ∈ t', a.deducedP) := by
  unfold internal
  split
  case isTrue =>
    simp
    intro btrue heq bfalse
    simp[btrue] at bfalse
  case isFalse hsat =>
    split
    case isTrue hcon =>
      split
      case isTrue hexi => exact internal_all_deduced_if_con
      case isFalse hexi =>
        simp[ALit.decidedP_iff_decidedB, ←ALit.ded_iff_not_dec] at hexi
        intro heq bfalse
        simp at heq
        simp[←heq.2]
        constructor
        case left => simpa using hcon
        case right => exact hexi
    case isFalse hcon =>
      simp
      split
      case isTrue hunit =>
        exact internal_all_deduced_if_con
      case isFalse hunit =>
        exact internal_all_deduced_if_con
  termination_by distance t v vz
  decreasing_by
    have : t.length < v := by
      rename ¬decide (t⊨f) = true => sat
      rename ¬decide (t⊭f) = true => con
      simp at sat con
      have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
      simp[Trail.names] at this
      exact this
    exact distance_dec this
    have : t.length < v := by
      rename ¬decide (t⊨f) = true => sat
      rename ¬decide (t⊭f) = true => con
      simp at sat con
      have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
      simp[Trail.names] at this
      exact this
    exact distance_prop this
    have : t.length ≤ v := Trail.mem_vwf twf.1 twf.2 wf.2
    exact distance_bc this

theorem internal_com_preserved {f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}:
  internal t f v vz wf twf com = (b, t') → Completenes.inv t' f := by
  unfold internal
  split
  case isTrue hsat =>
    intro heq
    simp at heq
    rw[←heq.2]
    exact com
  case isFalse hsat =>
    split
    case isTrue hcon =>
      split
      case isTrue exdec=>
        intro h
        simp at h
        exact internal_com_preserved h
      case isFalse exdec =>
        intro heq
        simp at heq
        rw[←heq.2]
        exact com
    case isFalse hcon =>
      simp
      split
      case isTrue exuni =>
        exact internal_com_preserved
      case isFalse exuni =>
        exact internal_com_preserved
  termination_by distance t v vz
  decreasing_by
    have : t.length < v := by
      rename ¬decide (t⊨f) = true => sat
      rename ¬decide (t⊭f) = true => con
      simp at sat con
      have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
      simp[Trail.names] at this
      exact this
    exact distance_dec this
    have : t.length < v := by
      rename ¬decide (t⊨f) = true => sat
      rename ¬decide (t⊭f) = true => con
      simp at sat con
      have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
      simp[Trail.names] at this
      exact this
    exact distance_prop this
    have : t.length ≤ v := Trail.mem_vwf twf.1 twf.2 wf.2
    exact distance_bc this

theorem DPLL.com_preserved {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail} :
  DPLL f v wf = (b, t) → Completenes.inv t f := by
  simp[DPLL]
  cases f
  case nil =>
    simp
    intro btrue heq
    simp[heq, Completenes.inv]
  case cons c cs =>
    simp
    intro h
    exact internal_com_preserved h


theorem DPLL.all_deduced_if_con {f : Formula}{v : Variables} {wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail} :
  DPLL f v wf = (b, t) → b = false → t ⊭ f ∧ ∀ a ∈ t, a.deducedP := by
  simp[DPLL]
  cases f
  case nil =>
    simp
    intro btrue hnil bfalse
    simp[btrue] at bfalse
  case cons x xs =>
    simp
    intro heq bfalse
    exact internal_all_deduced_if_con heq bfalse


theorem DPLL.soundness {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail} :
  DPLL f  v wf = (b, t) → b = true → ∃ (t : Trail), t ⊨ f := by
  intro h bh
  have := DPLL.final_state h
  simp[bh] at this
  exists t

theorem DPLL.final_false{f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}:
  DPLL f v wf = (b, t) → b = false → ¬ (∃ (t : Trail), t.wf ∧ t ⊨ f) := by
  intro heq bfalse
  have state := DPLL.all_deduced_if_con heq bfalse
  have com := DPLL.com_preserved heq
  have := Completenes.inv_completeness twf.1 com state.2
  simp at this ⊢
  intro x xwf
  have nohead := Completenes.from_con state.1
  simp at nohead


  intro h
  unfold internal at h
  split at h
  case isTrue hsat => simp at h
  case isFalse hsat =>
    split at h
    case isTrue hcon =>
      simp at h
      split at h
      case isTrue hexi =>
        exact internal_final_false h
      case isFalse hexi =>
        simp at hexi



theorem DPLL.completeness {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}:
  (∃ (t : Trail), t ⊨ f) → ∃ (t : Trail), DPLL f v wf = (true, t) := by
  intro h
  obtain ⟨ t, tsat ⟩ := h
  simp[DPLL]
  split
  case h_1 => simp
  case h_2 f wf hd tl wf' =>
    unfold internal
    split
    case isTrue hsat => simp
    case isFalse hsat =>
      split
      case isTrue hcon =>
        simp[Conflict.con, Trail.lits] at hcon
        simp[Formula.wf, Clause.wf] at wf'
        have := wf'.1.1.1.1
        obtain ⟨ l, ls, lmem ⟩ := List.ne_nil_iff_exists_cons.mp this
        cases hcon
        case inl hcon =>
          simp[lmem] at hcon
          have := hcon l
          simp at this
        case inr hcon =>
          obtain ⟨ c, cmem, call ⟩ := hcon
          have := (wf'.1.2 c cmem).1.1
          obtain ⟨ l, ls, lmem ⟩ := List.ne_nil_iff_exists_cons.mp this
          simp[lmem] at call
          have := call l
          simp at this
      case isFalse hcon =>
        simp
        split
