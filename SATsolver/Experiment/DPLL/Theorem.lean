import SATsolver.Experiment.DPLL.impl

theorem internal_final_state{f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}:
  internal t f v vz wf twf = (b, t') → t' ⊨ f ∨ b = false := by
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


theorem DPLL.soundness {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail} :
  DPLL f  v wf = (b, t) → b = true → ∃ (t : Trail), t ⊨ f := by
  intro h bh
  have := DPLL.final_state h
  simp[bh] at this
  exists t

theorem internal_final_false{f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}:
  internal t f v vz wf twf = (false, t') → ¬ (∃ (t : Trail), t ⊨ f) := by
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
