import SATsolver.Experiment.Relations.Theories
import SATsolver.Experiment.DPLL.misc

def backtrack (t : Trail)(wf : ∃ a ∈ t, a.decidedP)(twf : t.wf) : Trail :=
  have : t ≠ [] := by
    intro contra
    simp[contra] at wf
  match t with
  | a::as =>
    match a with
    | .decided l => (ALit.deduced l.negate)::as
    | .deduced _ =>
      have aswf : Trail.wf as := by
        simp[Trail.wf, Trail.names] at twf ⊢
        simp[twf]
        exact twf.2.2
      have : (∃ a ∈ as, a.decidedP) := by
        obtain ⟨ a, amem, adec ⟩ := wf
        rw[ALit.dec_is_dec] at adec
        obtain ⟨ l, ha ⟩ := adec
        simp [ha] at amem
        exists a
        simp[ha, amem, ALit.decidedP]
      backtrack as this aswf

theorem backtrack_lemma {hd tl : Trail}{a : ALit}{wf: ∃ e ∈ (hd++a::tl), e.decidedP}{twf : (hd++a::tl).wf} :
  (∀ e ∈ hd, ¬ e.decidedP) → a.decidedP → backtrack (hd++a::tl) wf twf = (ALit.deduced a.lit.negate)::tl := by
  intro hhd ha
  cases a
  case deduced => simp[ALit.decidedP] at ha
  case decided l =>
    induction hd
    case nil =>
      simp[backtrack, ALit.lit]
    case cons x xs ih =>
      have hhd2 : (∀ (e : ALit), e ∈ xs → ¬e.decidedP) := by
        intro a amem
        have : a ∈ x::xs := by simp[List.mem_cons, amem]
        exact hhd a this
      have wf2 : ∃ e, e ∈ xs ++ (ALit.decided l)::tl ∧ e.decidedP := by
        obtain ⟨ e, emem, he ⟩ := wf
        cases emem
        case head => have := hhd x; simp at this; contradiction
        case tail hmem => exists e
      cases x
      case decided l =>
        have := hhd (ALit.decided l)
        simp[ALit.decidedP] at this
      case deduced =>
        simp[backtrack]
        exact ih hhd2


theorem bck_preserves_twf {t : Trail}{f : Formula}
{wf : ∃ a ∈ t, a.decidedP}{twf : t.wf}{tf : ∀ n ∈ t.names, n ∈ f.names} :
(backtrack t wf twf).wf ∧ ∀ n ∈ (backtrack t wf twf).names, n ∈ f.names := by
  obtain ⟨ hd, tl, a, heq, ha, hhd ⟩  := exists_split_on_prop ALit.decidedP t wf
  rw[heq] at wf twf
  have bck_lemma : backtrack (hd++a::tl) wf twf = (ALit.deduced a.lit.negate)::tl := backtrack_lemma hhd ha
  have names : Trail.names (a :: tl) = Trail.names (ALit.deduced a.lit.negate :: tl) := by
    simp[Trail.names, ALit.name, Lit.name_name_negate, ALit.lit]
    cases a
    all_goals simp
  simp[heq, bck_lemma, ←names] at ⊢
  constructor
  case left =>
    have wf := Trail.wf_append twf
    simp[Trail.wf] at wf
    simp[←names, Trail.wf, wf]
  case right =>
    intro n nmem
    rw[heq, Trail.names_append] at tf
    exact tf n (by simp[nmem])

theorem dedwf_tl {f hd a tl} : (∀ (x : ALit), x ∈ hd → ¬x.decidedP) → a.decidedP → Trail.deduction_wf f (hd ++ a :: tl) → Trail.deduction_wf f tl := by
    intro hdall adec h
    induction hd
    case nil =>
      cases a
      case decided l =>
        simp[Trail.deduction_wf] at h
        exact h
      case deduced =>
        simp[ALit.decidedP] at adec
    case cons hhd hd ih =>
      have hdall' : ∀ (x : ALit), x ∈ hd → ¬x.decidedP := by
        intro x xmem
        exact hdall x (by simp[xmem])
      have : Trail.deduction_wf f (hd ++ a :: tl) := by
        cases hhd
        case decided =>
          simp[Trail.deduction_wf] at h
          exact h
        case deduced =>
          simp[Trail.deduction_wf] at h
          exact h.2
      exact ih this (hdall := hdall')


theorem bck_deduction_inv {f : Formula}{t : Trail}{wf : ∃ a ∈ t, a.decidedP}{twf : t.wf}:
  t.deduction_wf f → t ⊭ f →  Trail.deduction_wf f (backtrack t wf twf) := by
  intro hwf con
  induction t
  case nil => simp at wf
  case cons hd tl ih =>
    cases hd
    case decided l =>
      simp[backtrack, Trail.deduction_wf]
      constructor
      case left =>
        intro hd hdwf
        left
        have := (Trail.con_cons_con con) hd
        simp[Lit.negneg, this]
      case right =>
        simp[Trail.deduction_wf] at hwf
        exact hwf
    case deduced l =>
      obtain ⟨ hd, tl', a, heq, adec, hdall ⟩ := exists_split_on_prop ALit.decidedP (ALit.deduced l :: tl) wf
      simp[heq] at ⊢ twf
      rw[heq] at wf
      have := backtrack_lemma hdall adec (twf := twf) (wf := wf)
      simp[this, Trail.deduction_wf]
      constructor



      have hwf' : Trail.deduction_wf f tl := hwf.2
      have wf' : ∃ a, a ∈ tl ∧ a.decidedP := by
        obtain ⟨ a, amem, adec ⟩ := wf
        cases a
        case decided k =>
          simp at amem
          exists ALit.decided k
        case deduced k =>
          simp [ALit.decidedP] at adec
      have twf' : Trail.wf tl := Trail.wf_cons twf
      obtain ⟨ hd', tl', a, heq, adec,hall⟩  := exists_split_on_prop ALit.decidedP tl wf'
      subst heq
      have : backtrack (hd' ++ a :: tl') wf' twf' = ALit.deduced (a.lit.negate)::tl' := backtrack_lemma hall adec
      rw[this]
