import SATsolver.Experiment.Relations.Theories

def backtrack (t : Trail)(wf : ∃ a ∈ t, a.decidedP) : Trail :=
  have : t ≠ [] := by
    intro contra
    simp[contra] at wf
  match t with
  | a::as =>
    match a with
    | .decided l => (ALit.deduced l.negate)::as
    | .deduced _ =>
      have : (∃ a ∈ as, a.decidedP) := by
        obtain ⟨ a, amem, adec ⟩ := wf
        rw[ALit.dec_is_dec] at adec
        obtain ⟨ l, ha ⟩ := adec
        simp [ha] at amem
        exists a
        simp[ha, amem, ALit.decidedP]
      backtrack as this

theorem backtrack_lemma {hd tl : Trail}{a : ALit}{wf: ∃ e ∈ (hd++a::tl), e.decidedP} :
  (∀ e ∈ hd, ¬ e.decidedP) → a.decidedP → backtrack (hd++a::tl) wf = (ALit.deduced a.lit.negate)::tl := by
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
