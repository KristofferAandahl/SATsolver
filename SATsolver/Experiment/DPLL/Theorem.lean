import SATsolver.Experiment.DPLL.impl

theorem internal_final_state{f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}:
  internal t f v vz wf twf com = (b, t') → (b = true ∧ t' ⊨ f) ∨ b = false := by
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
DPLL f  v wf = (b, t) → (b = true ∧ t ⊨ f) ∨ b = false := by
  simp[DPLL]
  cases f
  case nil => simp[Satisfies.sat]
  case cons c cs =>
    simp
    exact internal_final_state


theorem internal_wf{f: Formula}{v : Variables}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}:
  internal t f v vz wf twf com = (b, t') → t'.wf := by
  unfold internal
  split
  case isTrue hsat =>
    simp at hsat ⊢
    intro bh heq
    simp[←heq, twf.1]
  case isFalse hsat =>
    split
    case isTrue hcon =>
      split
      case isTrue exDec =>
        intro h
        exact internal_wf h
      case isFalse exDec =>
        simp
        intro bh th
        simp[←th, twf.1]
    case isFalse hcon =>
      simp
      split
      case isTrue hunit =>
        intro h
        exact internal_wf h
      case isFalse hunit =>
        intro h
        exact internal_wf h
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


theorem DPLL.wf{f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail}:
DPLL f  v wf = (b, t) → t.wf := by
  simp[DPLL]
  cases f
  case nil => simp; intro bh heq; simp[heq, Trail.wf, Trail.names]
  case cons c cs =>
    simp
    exact internal_wf


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
  DPLL f  v wf = (b, t) → b = true → ∃ (t : Trail), t.wf ∧ t ⊨ f := by
  intro h bh
  have fs := DPLL.final_state h
  have wf := DPLL.wf h
  simp[bh] at fs
  exists t

theorem DPLL.final_false {b : Bool}{f: Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{t : Trail}{twf : t.wf}:
  DPLL f v wf = (b, t) → b = false → ¬ (∃ (t : Trail), t.wf ∧ t ⊨ f) := by
  intro heq bfalse
  have state := DPLL.all_deduced_if_con heq bfalse
  have com := DPLL.com_preserved heq
  have := Completenes.inv_completeness twf com state.2
  simp at this ⊢
  intro x xwf
  have nohead := Completenes.con_no_exist state.1
  simp at nohead
  exact this nohead x xwf


theorem DPLL.completeness {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}:
  (∃ (t : Trail), t.wf ∧ t ⊨ f) → ∃ (t : Trail), DPLL f v wf = (true, t) := by
  intro h
  obtain ⟨ t, twf, tsat ⟩ := h
  let dpll : (Bool ×  Trail) := DPLL f v wf
  let b := dpll.1
  let t' := dpll.2
  have dplleq : DPLL f v wf = (b, t') := by simp[dpll, b ,t']
  have := DPLL.final_state dplleq
  cases this
  case inl lh =>
    exists t'
    rw[dplleq, lh.1]
  case inr rh =>
    have := DPLL.wf dplleq
    have := DPLL.final_false (twf := this) dplleq rh
    simp at this
    have := this t twf
    contradiction


theorem final_state_moma {f: Formula}{v : Variables}{occ : List (Nat × Nat)}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}{hocc : occ = occurences f v wf}:
  internal_moma t f v occ vz wf twf com hocc = (b, t') → (b = true ∧ t' ⊨ f) ∨ b = false := by
  unfold internal_moma
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
        exact final_state_moma h
      case isFalse exDec =>
        simp
        intro bh th
        simp[bh]
    case isFalse hcon =>
      simp
      split
      case isTrue hunit =>
        intro h
        exact final_state_moma h
      case isFalse hunit =>
        intro h
        exact final_state_moma h
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

theorem DPLL_moma.final_state{f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail}:
DPLL_moma f  v wf = (b, t) → (b = true ∧ t ⊨ f) ∨ b = false := by
  simp[DPLL_moma]
  cases f
  case nil => simp[Satisfies.sat]
  case cons c cs =>
    simp
    exact final_state_moma

theorem moma_wf{f: Formula}{v : Variables}{occ : List (Nat × Nat)}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}{hocc : occ = occurences f v wf}:
  internal_moma t f v occ vz wf twf com hocc = (b, t') → t'.wf := by
  unfold internal_moma
  split
  case isTrue hsat =>
    simp at hsat ⊢
    intro bh heq
    simp[←heq, twf.1]
  case isFalse hsat =>
    split
    case isTrue hcon =>
      split
      case isTrue exDec =>
        intro h
        exact moma_wf h
      case isFalse exDec =>
        simp
        intro bh th
        simp[←th, twf.1]
    case isFalse hcon =>
      simp
      split
      case isTrue hunit =>
        intro h
        exact moma_wf h
      case isFalse hunit =>
        intro h
        exact moma_wf h
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


theorem DPLL_moma.wf{f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail}:
DPLL_moma f  v wf = (b, t) → t.wf := by
  simp[DPLL_moma]
  cases f
  case nil => simp; intro bh heq; simp[heq, Trail.wf, Trail.names]
  case cons c cs =>
    simp
    exact moma_wf


theorem moma_all_deduced_if_con{f: Formula}{v : Variables}{occ : List (Nat × Nat)}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}{hocc : occ = occurences f v wf}:
  internal_moma t f v occ vz wf twf com hocc = (b, t') → b = false → (t' ⊭ f ∧  ∀ a ∈ t', a.deducedP) := by
  unfold internal_moma
  split
  case isTrue =>
    simp
    intro btrue heq bfalse
    simp[btrue] at bfalse
  case isFalse hsat =>
    split
    case isTrue hcon =>
      split
      case isTrue hexi => exact moma_all_deduced_if_con
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
        exact moma_all_deduced_if_con
      case isFalse hunit =>
        exact moma_all_deduced_if_con
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

theorem moma_com_preserved {f: Formula}{v : Variables}{occ : List (Nat × Nat)}{vz : v ≠ 0}{wf : f.wf ∧ v.wf f}{b : Bool}{t t' : Trail}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}{com : Completenes.inv t f}{hocc : occ = occurences f v wf}:
  internal_moma t f v occ vz wf twf com hocc = (b, t') → Completenes.inv t' f := by
  unfold internal_moma
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
        exact moma_com_preserved h
      case isFalse exdec =>
        intro heq
        simp at heq
        rw[←heq.2]
        exact com
    case isFalse hcon =>
      simp
      split
      case isTrue exuni =>
        exact moma_com_preserved
      case isFalse exuni =>
        exact moma_com_preserved
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

theorem DPLL_moma.com_preserved {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail} :
  DPLL_moma f v wf = (b, t) → Completenes.inv t f := by
  simp[DPLL_moma]
  cases f
  case nil =>
    simp
    intro btrue heq
    simp[heq, Completenes.inv]
  case cons c cs =>
    simp
    intro h
    exact moma_com_preserved h


theorem DPLL_moma.all_deduced_if_con {f : Formula}{v : Variables} {wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail} :
  DPLL_moma f v wf = (b, t) → b = false → t ⊭ f ∧ ∀ a ∈ t, a.deducedP := by
  simp[DPLL_moma]
  cases f
  case nil =>
    simp
    intro btrue hnil bfalse
    simp[btrue] at bfalse
  case cons x xs =>
    simp
    intro heq bfalse
    exact moma_all_deduced_if_con heq bfalse


theorem DPLL_moma.soundness {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{b : Bool}{t : Trail} :
  DPLL_moma f  v wf = (b, t) → b = true → ∃ (t : Trail), t.wf ∧ t ⊨ f := by
  intro h bh
  have fs := DPLL_moma.final_state h
  have wf := DPLL_moma.wf h
  simp[bh] at fs
  exists t

theorem DPLL_moma.final_false {b : Bool}{f: Formula}{v : Variables}{wf : f.wf ∧ v.wf f}{t : Trail}{twf : t.wf}:
  DPLL_moma f v wf = (b, t) → b = false → ¬ (∃ (t : Trail), t.wf ∧ t ⊨ f) := by
  intro heq bfalse
  have state := DPLL_moma.all_deduced_if_con heq bfalse
  have com := DPLL_moma.com_preserved heq
  have := Completenes.inv_completeness twf com state.2
  simp at this ⊢
  intro x xwf
  have nohead := Completenes.con_no_exist state.1
  simp at nohead
  exact this nohead x xwf


theorem DPLL_moma.completeness {f : Formula}{v : Variables}{wf : f.wf ∧ v.wf f}:
  (∃ (t : Trail), t.wf ∧ t ⊨ f) → ∃ (t : Trail), DPLL_moma f v wf = (true, t) := by
  intro h
  obtain ⟨ t, twf, tsat ⟩ := h
  let dpll : (Bool ×  Trail) := DPLL_moma f v wf
  let b := dpll.1
  let t' := dpll.2
  have dplleq : DPLL_moma f v wf = (b, t') := by simp[dpll, b ,t']
  have := DPLL_moma.final_state dplleq
  cases this
  case inl lh =>
    exists t'
    rw[dplleq, lh.1]
  case inr rh =>
    have := DPLL_moma.wf dplleq
    have := DPLL_moma.final_false (twf := this) dplleq rh
    simp at this
    have := this t twf
    contradiction
