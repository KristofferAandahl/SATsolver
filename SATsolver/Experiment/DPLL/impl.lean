import SATsolver.Experiment.Relations.Theories
import SATsolver.Experiment.DPLL.distance



def internal (t : Trail)(f : Formula)(v : Variables)(vz : v ≠ 0)(wf : f.wf ∧ v.wf f)(twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names)(com : Completenes.inv t f): Bool × Trail :=
  if sat : decide (t ⊨ f) then
    (true, t)
  else if con : decide (t ⊭ f) then
    if anyDec : t.any ALit.decidedB then
      have bcwf : ∃ a ∈ t, a.decidedP := by
        simp[ALit.decidedP_iff_decidedB] at anyDec
        obtain ⟨ a, amem, adec ⟩ := anyDec
        exists a
      have com' : Completenes.inv (backtrack t bcwf twf.1) f := by
        simp at con
        have := Completenes.from_con con
        exact bck_completeness2 (twf := twf.1) (wf := bcwf) com this
      internal (backtrack t bcwf twf.1) f v vz wf (bck_preserves_twf (tf := twf.2)) com'
    else (false, t)
  else
    let copt := f.find? (fun c => c.unit t)
    if h : copt.isSome then
      let c := copt.get h
      have : c.unit t := by
        have cunit : copt = some c := by
          simp[c]
        simp[copt] at cunit
        have := List.find?_some cunit
        simp at this
        exact this
      have cmem : c ∈ f := by
        simp only [copt] at h
        have := List.get_find?_mem h
        simp[c, copt, this]
      have com' : Completenes.inv (propogate t c this) f := by
        exact ppg_completeness2 twf wf.1 com cmem
      internal (propogate t c this) f v vz wf (ppg_preserves_wf cmem (fwf := wf.1) (twf := twf)) com'
    else
      have ud : t¿f := by
        simp at *
        exact Formula.nSatCon_ud sat con
      let copt := (f.find? (t¿·))
      have csome : copt.isSome := by
        have := Formula.ud_iff_exists_csUD.mp ud
        simp[copt, this]
      let c := copt.get csome
      have : t ¿ c := by
        have heq : copt = some c := by
          simp[c]
        simp[copt] at heq
        have := List.find?_some heq
        simp at this
        exact this
      let lopt := (c.find? (t¿·))
      have lsome : lopt.isSome := by
        have := Clause.ud_exists_lUd this
        simp[lopt, this]
      let l := lopt.get lsome
      have : t ¿ l := by
        have heq : lopt = some l := by
          simp[l]
        simp[lopt] at heq
        have := List.find?_some heq
        simp at this
        exact this
      have lmem : l.name ∈ f.names := by
        simp[Formula.names]
        exists c
        constructor
        case left =>
          simp only [copt] at csome
          have := List.get_find?_mem csome
          simp[c, copt, this]
        case right =>
          apply Clause.mem_mem_name
          simp only[lopt] at lsome
          have := List.get_find?_mem lsome
          simp[l, lopt, this]
      have com' : Completenes.inv (dec l t this) f := by
        exact dec_preserves_completenes lmem com
      internal (dec l t this) f v vz wf (dec_preserves_wf (fwf := wf.1) (twf := twf) lmem) com'
termination_by distance t v vz
decreasing_by
  have : t.length ≤ v := Trail.mem_vwf twf.1 twf.2 wf.2
  exact distance_bc this
  have : t.length < v := by
    simp at sat con
    have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
    simp[Trail.names] at this
    exact this
  exact distance_prop this
  have : t.length < v := by
    simp at sat con
    have := Trail.ud_vars twf.1 wf.1 wf.2 twf.2 (Formula.nSatCon_ud sat con)
    simp[Trail.names] at this
    exact this
  exact distance_dec this


def DPLL(f : Formula)(v : Variables)(wf : f.wf ∧ v.wf f) :=
  match f with
  | [] => (true, [])
  | hd::tl => internal [] (hd::tl) v (Variables.f_cons_ne_zero wf.2 (fwf := wf.1)) wf (by simp[Trail.wf, Trail.names]) (by simp[Completenes.inv])
