import SATsolver.Experiment.Relations.Theories

namespace Completenes

theorem sat_eq_not_con_or_ud {t : Trail}{f : Formula}:
  t.wf → (t ⊨ f ↔ ¬ (t ⊭ f ∨ t ¿ f)) := by
  intro twf
  simp[Satisfies.sat, Conflict.con, Undecided.ud]
  constructor
  case mp =>
    intro call
    constructor
    case left =>
      intro c cmem
      obtain ⟨ l, lc, lt ⟩ := call c cmem
      exists l
      constructor
      case left => exact lc
      case right =>
        intro contra
        have := Trail.lit_and_litn_not_wf lt contra
        contradiction
    case right =>
      intro c cmem l lmem hname
      obtain ⟨ l, lc, lt ⟩ := call c cmem
      exists l
      constructor
      case left => exact lc
      case right =>
        constructor
        case left => exact Trail.mem_lits_mem_names lt
        case right =>
          intro contra
          have := Trail.lit_and_litn_not_wf lt contra
          contradiction
  case mpr =>
    intro h c cmem
    obtain ⟨ l, lc, lt ⟩ := h.1 c cmem
    have := h.2 c cmem l lc
    by_cases lmem : l ∈ t.lits
    case pos => exists l
    case neg =>
      have hname :¬l.name ∈ t.names := by
        intro contra
        rw[←Trail.mem_lits_names_eq] at contra
        simp[lmem, lt] at contra
      obtain ⟨ j, jmem, heq ⟩  := this hname
      exists j
      constructor
      case left => exact jmem
      case right =>
        have := Trail.mem_lits_names_eq.mpr heq.1
        simp[heq.2] at this
        exact this


theorem con_no_exist {tl : Trail}{f : Formula} :
  tl ⊭ f → ¬ ∃ hd, Trail.wf (hd++tl) ∧ hd ++tl ⊨ f := by
  simp[Conflict.con, Satisfies.sat]
  intro c cmem call hd hdwf
  exists c
  constructor
  case left => exact cmem
  case right =>
    intro l lmem
    have negmem := call l lmem
    have lname : l.name ∈ Trail.names (hd++tl) := by
      have := Trail.mem_lits_mem_names negmem
      simp[Lit.name_name_negate] at this
      simp[Trail.names] at this  ⊢
      right; exact this
    have := Trail.lit_of_wf lname hdwf
    cases this
    case inl lh =>
      have := lh.2
      have : l.negate ∈ (hd ++ tl).lits := by
        simp[Trail.lits] at negmem ⊢
        right; exact negmem
      contradiction
    case inr rh =>
      exact rh.1

theorem modifier {tl : Trail}{f : Formula}{a : ALit}:
  (¬ ∃ hd, (hd++a::tl) ⊨ f) → (¬ ∃ hd, (hd++tl) ⊨ f) := by
  simp
  intro ah hd
  have := ah hd
  simp[Satisfies.sat] at this ⊢
  obtain ⟨ c, cmem, call ⟩ := this
  exists c
  constructor
  case left => exact cmem
  case right =>
    intro l lmem
    have := call l lmem
    simp[Trail.lits] at this ⊢
    constructor
    case left => exact this.1
    case right => exact this.2.2

def invariant (t : Trail)(f : Formula) : Prop :=
  match t with
  | [] => True
  | (ALit.decided _)::tl => invariant tl f
  | (ALit.deduced l)::tl => (¬ ∃ (hd : Trail), Trail.wf (hd++tl) ∧ (hd++tl) ⊨ f ∧ l.negate ∈ hd.lits) ∧ invariant tl f

theorem cons {a : ALit}{t : Trail}{f : Formula}:
  Completenes.invariant (a::t) f → Completenes.invariant t f := by
  intro h
  cases a
  case decided l => simpa [invariant] using h
  case deduced l => exact h.2

theorem append {hd tl : Trail}{f : Formula}:
  Completenes.invariant (hd++tl) f → Completenes.invariant tl f := by
  intro h
  induction hd
  case nil => simpa using h
  case cons x xs ih => exact ih (cons h)

theorem helper {l : Lit}{tl : Trail}{f : Formula} :
  Trail.wf ((ALit.deduced l)::tl) → invariant ((ALit.deduced l)::tl) f → (¬ ∃ hd, (hd++(ALit.deduced l)::tl) ⊨ f) → (¬ ∃ hd, Trail.wf (hd++tl) ∧ hd ++tl ⊨ f) := by
  intro twf hinv h hd
  have := modifier h
  simp at this
  obtain ⟨ hd, hdwf, hdsat ⟩ := hd
  have := this hd
  contradiction


def inv (t : Trail)(f : Formula) : Prop :=
  match t with
  | [] => true
  | (ALit.decided _)::tl => inv tl f
  | (ALit.deduced l)::tl => inv tl f ∧ (∀ hd, Trail.wf (hd++tl) ∧ hd++tl ⊨ f → l.name ∈ hd.names → l ∈ hd.lits)


theorem inv_completeness {t : Trail}{f : Formula} :
  t.wf → inv t f → (∀ a ∈ t, a.deducedP) → ¬(∃ hd, (hd++t).wf ∧ hd++t ⊨ f) → ¬ ∃ (t' : Trail), t'.wf ∧ t' ⊨ f := by
  simp
  intro twf hinv hall hcon t' t'wf
  induction t
  case nil =>
    simp at *
    exact hcon t' t'wf
  case cons x xs ih =>
    have wfxs := Trail.wf_cons twf
    cases x
    case decided l =>
      have := hall (ALit.decided l) (by simp)
      simp[ALit.deducedP] at this
    case deduced l =>
      have invxs := hinv.1
      have xsall : ∀ (a : ALit), a ∈ xs → a.deducedP := by
        intro a amem
        exact hall a (by simp[amem])
      have xscon : (∀ (x : Trail), (x ++ xs).wf → ¬x ++ xs⊨f):= by
        intro hd wfapp
        let hdrem := hd.remove (ALit.deduced l).name
        have := Trail.wfapp_wfremapp wfapp twf
        intro contra
        apply hcon hdrem this
        have mem_names := hinv.2 hd (And.intro wfapp contra)
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
          simp [Trail.lits] at rh ⊢
          simp[rh]
      exact ih wfxs invxs xsall xscon
