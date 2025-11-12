import SATsolver.Experiment.Relations.Theories
import SATsolver.Experiment.DPLL.distance

def internal (t : Trail)(f : Formula)(wf : f ≠ []): Bool :=
  if sat : decide (t ⊨ f) then
    true
  else if con : decide (t ⊭ f) then
    if anyDec : t.any ALit.decidedB then
      have bcwf : ∃ a ∈ t, a.decidedP := by
        simp[ALit.decidedP_iff_decidedB] at anyDec
        obtain ⟨ a, amem, adec ⟩ := anyDec
        exists a
      internal (backtrack t bcwf) f wf
    else false
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
      internal (propogate t c this) f wf
    else
      have ud : t¿f := by
        simp at *
        exact Formula.nSatCon_ud sat con
      let copt := (f.find? (t¿·))
      have : copt.isSome := by
        have := Formula.ud_iff_exists_csUD.mp ud
        simp[copt, this]
      let c := copt.get this
      have : t ¿ c := by
        have heq : copt = some c := by
          simp[c]
        simp[copt] at heq
        have := List.find?_some heq
        simp at this
        exact this
      let lopt := (c.find? (t¿·))
      have : lopt.isSome := by
        have := Clause.ud_exists_lUd this
        simp[lopt, this]
      let l := lopt.get this
      have : t ¿ l := by
        have heq : lopt = some l := by
          simp[l]
        simp[lopt] at heq
        have := List.find?_some heq
        simp at this
        exact this
      internal (dec l t this) f wf
termination_by distance t f wf
decreasing_by
  have : f.names.eraseDups.length > t.length := by sorry
  exact distance_bc this
  have : f.names.eraseDups.length > t.length := by sorry
  exact distance_prop this
  have : f.names.eraseDups.length > t.length := by sorry
  exact distance_dec this
