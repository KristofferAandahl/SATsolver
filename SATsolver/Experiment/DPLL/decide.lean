import SATsolver.Experiment.Relations.Theories

def dec (l : Lit)(t : Trail)(_ : t ¿ l): Trail :=
  ALit.decided l :: t

theorem dec_preserves_wf{l : Lit}{t : Trail}{lud : t ¿ l}{f : Formula}
  {fwf : f.wf}{twf : t.wf ∧ ∀ n ∈ t.names, n ∈ f.names}:
  l.name ∈ f.names → (dec l t lud).wf ∧ ∀ n ∈ (dec l t lud).names, n ∈ f.names := by
  intro lmem
  simp[Undecided.ud] at lud
  constructor
  case left =>
    have : 0 ≠ l.name := by
      intro contra
      simp[Formula.wf, Clause.wf] at fwf
      simp[Formula.names] at lmem
      obtain ⟨ c, cmem, cname ⟩ := lmem
      simp[←contra, (fwf c cmem).1.2.2] at cname
    simp[Trail.wf, dec, Trail.names_cons, ALit.name, lud, twf.1.1, twf.1.2, this]
  case right =>
    intro n nmem
    simp[dec] at nmem
    cases nmem
    case head => simp[ALit.name, lmem]
    case tail tail => exact twf.2 n tail
