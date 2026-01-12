import SATsolver.Experiment.Relations.Theories
import SATsolver.Experiment.DPLL.misc
import SATsolver.Experiment.DPLL.completeness

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

theorem dedwf_tl {f hd a tl} :
(∀ (x : ALit), x ∈ hd → ¬x.decidedP) → a.decidedP → Trail.deduction_wf f (hd ++ a :: tl) → Trail.deduction_wf f tl := by
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

theorem helper1 :
  Trail.wf (ALit.deduced l :: t) → Trail.deduction_wf f (ALit.deduced l :: t) → (ALit.deduced l :: t) ⊭ f →
  ∀ hd, Trail.wf (hd++t) → hd++t ⊭ f ∨ hd++t ¿ f := by
  intro twf dedwf hcon hd hdwf
  simp[Trail.deduction_wf] at dedwf
  have := dedwf.1 hd hdwf
  by_cases lmem : l ∈ hd.lits
  case pos =>
    simp[Conflict.con] at hcon ⊢
    obtain ⟨ c, cmem, call ⟩ := hcon
    left
    exists c
    constructor
    case left => exact cmem
    case right =>
      intro j jmem
      have := call j jmem
      simp[Trail.lits] at this ⊢
      cases this
      case inl lh =>
        simp[ALit.lit] at lh
        rw[lh]
        have := Trail.mem_lits_exists_mem lmem
        simp[this]
      case inr rh => simp[rh]
  case neg =>
    by_cases lnmem : l.negate ∈ hd.lits
    case pos => exact this lnmem
    case neg =>
      have namenin : l.name ∉ hd.names := by
        simp[←Trail.mem_lits_names_eq, lmem, lnmem]
      simp[Conflict.con] at hcon
      obtain ⟨ c, cmem, call ⟩ := hcon
      simp[con_or_ud]
      exists c
      constructor
      case left => exact cmem
      case right =>
        intro j jmem
        have := call j jmem
        simp[Trail.lits, Trail.names] at this namenin ⊢
        cases this
        case inl lh =>
          have lh := congrArg Lit.name lh
          simp[ALit.lit, Lit.name_name_negate] at lh
          simp[lh] at *
          right
          constructor
          case left => exact namenin
          case right =>
            simp[Trail.wf, Trail.names] at twf
            exact twf.1.1
        case inr rh => left; right; exact rh



theorem bck_completeness2 {f : Formula}{t : Trail}{wf : ∃ a ∈ t, a.decidedP}{twf : t.wf}:
  Completenes.inv t f → (¬ ∃ hd, (hd++t).wf ∧ (hd++t) ⊨ f)  →  Completenes.inv (backtrack t wf twf) f := by
  intro hcom hcon
  induction t
  case nil => simp at wf
  case cons x xs ih =>
    cases x
    case decided l =>
      simp[backtrack, Completenes.inv]
      constructor
      case left => exact hcom
      case right =>
        intro hd hdwf hdsat lmem
        simp at hcon
        simp[←Trail.mem_lits_names_eq, Lit.negneg] at lmem
        cases lmem
        case inl lh => exact lh
        case inr rh =>
          let hd' : Trail := hd.remove (ALit.decided l).name
          have := Trail.wfapp_wfremapp hdwf twf
          have nsat := hcon hd' this
          obtain ⟨ a, amem, heq ⟩ := Trail.mem_lits_exists_mem rh
          have := (appsat_remapp_sat hdwf amem).mp hdsat
          simp[Satisfies.sat] at this nsat
          obtain ⟨ c, cmem, call ⟩ := nsat
          obtain ⟨ j, jc, jt ⟩ := this c cmem
          have := call j jc
          simp[hd', Trail.lits_append] at this jt
          cases jt
          case inl lh =>
            have := this.1
            simp[←ALit.name_name_lit] at lh this
            rw[heq] at lh
            simp[ALit.lit] at this
            contradiction
          case inr rh =>
            have := this.2
            simp[Trail.lits_cons] at rh this
            cases rh
            case inl lh =>
              simp[lh, heq] at this
              simp[ALit.lit] at this
            case inr rh2 =>
              have := this.2
              contradiction
    case deduced l=>
      simp[backtrack]
      have : (¬∃ (hd : Trail), (hd ++ xs).wf ∧ hd ++ xs⊨f) := by
        simp at hcon ⊢
        intro hd wfapp
        let hdrem := hd.remove (ALit.deduced l).name
        have := Trail.wfapp_wfremapp wfapp twf
        intro contra
        apply hcon hdrem this
        have mem_names := hcom.2 hd (And.intro wfapp contra)
        simp[Satisfies.sat] at contra ⊢
        intro c cmem
        obtain ⟨ j, jc, jt ⟩ := contra c cmem
        exists j
        simp[jc, hdrem, Trail.lits_append] at jt ⊢
        cases jt
        case inl lh =>
          obtain ⟨ a, amem, heq ⟩ := Trail.mem_lits_exists_mem lh
          by_cases heq2 : j = l
          case pos => simp[heq2, Trail.lits, ALit.lit]
          case neg =>
            by_cases hname : j.name = l.name
            case pos =>
              rw[←hname] at mem_names
              have := Trail.mem_lits_mem_names lh
              have := mem_names this
              obtain ⟨ b, bmem, bheq ⟩ := Trail.mem_lits_exists_mem this
              have : a ≠ b := by
                intro contra
                rw[←bheq, ←heq, contra] at heq2
                contradiction
              have := Trail.uniques (Trail.wf_append wfapp).1 this amem bmem
              simp[←ALit.name_name_lit, heq, bheq] at this
              contradiction
            case neg =>
              left
              simp[Trail.remove, Trail.lits]
              exists a
              simp[amem, heq, ←ALit.name_name_lit]
              intro contra
              rw[contra] at hname
              simp[ALit.lit] at hname
        case inr rh =>
          simp[Trail.lits_cons, rh]
      have wf' : ∃ a, a ∈ xs ∧ a.decidedP := by
        obtain ⟨ a, amem, adec ⟩ := wf
        simp at amem
        cases amem
        case inl lh =>
          rw[lh] at adec
          simp[ALit.decidedP] at adec
        case inr rh =>
          exists a
      have twf' : Trail.wf xs := by
        simp[Trail.wf, Trail.names] at twf ⊢
        constructor
        case left => exact twf.1.2
        case right => exact twf.2.2
      have hcoml := hcom.1
      exact ih hcoml this
