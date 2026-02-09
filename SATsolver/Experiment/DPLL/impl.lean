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
        have := Completenes.con_no_exist con
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
      have com' : Completenes.inv (propagate t c this) f := by
        exact ppg_completeness2 twf wf.1 com cmem
      internal (propagate t c this) f v vz wf (ppg_preserves_wf cmem (fwf := wf.1) (twf := twf)) com'
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


def occurences(f : Formula)(v : Variables)(_ : f.wf ∧ v.wf f) : List (Nat × Nat):=
  ((List.range v).map (fun n => ( n+1, f.names.count (n + 1) ))).mergeSort (fun (_,o₁) (_,o₂)=> o₁ >= o₂)

theorem n_f_n_occ {n : Nat}{f : Formula}{v : Variables}(wf : f.wf ∧ v.wf f):
  n ∈ f.names → ∃ o, (n, o) ∈ occurences f v wf := by
  intro nin
  have nzero : n ≠ 0 := by
    have := Formula.zero_not_names wf.1
    intro contra
    rw[contra] at nin
    contradiction
  simp[occurences, Variables.wf, Formula.wf] at wf ⊢
  have nlev := wf.2.1 n nin
  let o : Nat := f.names.count n
  let m : Nat := n -1
  have : m + 1 = n := by
    have : n > 0 := Nat.zero_lt_of_ne_zero nzero
    simp[m, this, Nat.sub_one_add_one_eq_of_pos]
  exists o, m
  simp[this, o]
  have mltn : m < n := by simp[←this]
  exact Nat.lt_of_lt_of_le mltn nlev

theorem nocc_nf{res : Nat × Nat}{f : Formula}{v : Variables}(wf : f.wf ∧ v.wf f):
  res ∈ occurences f v wf → res.1 ∈ f.names := by
  intro h
  simp[occurences] at h
  obtain ⟨ a, altv, ahen ⟩ := h
  simp[Formula.wf, Variables.wf] at wf
  have nlev : res.1 ≤ v := by
    have := Nat.succ_le_of_lt altv
    rw[← ahen, ←Nat.succ_eq_add_one]
    exact this
  have nnzero : res.1 ≠ 0 := by
    simp[← ahen]
  exact wf.2.2 res.1 nlev nnzero


def internal_moma (t : Trail)(f : Formula)(v : Variables) (occ : List (Nat × Nat))(vz : v ≠ 0)(wf : f.wf ∧ v.wf f)(twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names)(com : Completenes.inv t f)(hocc : occ = occurences f v wf): Bool × Trail :=
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
        have := Completenes.con_no_exist con
        exact bck_completeness2 (twf := twf.1) (wf := bcwf) com this
      internal_moma (backtrack t bcwf twf.1) f v occ vz wf (bck_preserves_twf (tf := twf.2)) com' hocc
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
      have com' : Completenes.inv (propagate t c this) f := by
        exact ppg_completeness2 twf wf.1 com cmem
      internal_moma (propagate t c this) f v occ vz wf (ppg_preserves_wf cmem (fwf := wf.1) (twf := twf)) com' hocc
    else
      have ud : t¿f := by
        simp at *
        exact Formula.nSatCon_ud sat con
      have nexi := Formula.ud_exists_udname ud
      let nopt := (occ.find? (fun (n,o) => n ∉ t.names))
      have nsome : nopt.isSome := by
        obtain ⟨ n, hn ⟩ := nexi
        have := n_f_n_occ wf hn.1
        simp[nopt, hocc]
        exists n
        simp[this, hn.2]
      let res := nopt.get nsome
      have : t ¿ (Lit.pos res.1) := by
        simp[Undecided.ud]
        have heq : nopt = some res := by simp[res]
        simp[nopt] at heq
        have := List.find?_some heq
        simp[Lit.name] at ⊢ this
        exact this
      have lmem : (Lit.pos res.1).name ∈ f.names := by
        have : res ∈ occ := by
          simp[res, nopt, List.get_find?_mem]
        simp[hocc] at this
        have := nocc_nf wf this
        simp[Lit.name]
        exact this
      have com' : Completenes.inv (dec (Lit.pos res.1) t this) f := by
        exact dec_preserves_completenes lmem com
      internal_moma (dec (Lit.pos res.1) t this) f v occ vz wf (dec_preserves_wf (fwf := wf.1) (twf := twf) lmem) com' hocc
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


def DPLL_moma(f : Formula)(v : Variables)(wf : f.wf ∧ v.wf f) :=
  match f with
  | [] => (true, [])
  | hd::tl =>
    let occ := occurences (hd::tl) v wf
    internal_moma [] (hd::tl) v occ (Variables.f_cons_ne_zero wf.2 (fwf := wf.1)) wf (by simp[Trail.wf, Trail.names]) (by simp[Completenes.inv]) (by simp[occ])
