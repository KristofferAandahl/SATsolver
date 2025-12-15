import SATsolver.Experiment.Data.ALit

abbrev Trail : Type := List ALit

namespace Trail

def lits : Trail → List Lit
  | t => t.map ALit.lit

theorem mem_mem_lits{t : Trail}{a : ALit} :
  a ∈ t → a.lit ∈ t.lits := by
  simp[lits]
  intro h
  exists a

theorem lits_append(hd tl : Trail):
  (hd++tl).lits = hd.lits++tl.lits := by
  simp[lits]

theorem lits_cons (hd: ALit)(tl : Trail):
  Trail.lits (hd::tl) = hd.lit::tl.lits := by
  simp[lits]

def names : Trail → List Nat
  |t => t.map ALit.name

theorem mem_mem_names{t : Trail}{a : ALit} :
  a ∈ t → a.name ∈ t.names := by
  simp[names]
  intro h
  exists a

theorem mem_name_exists_mem {t : Trail}{n : Nat} :
  n ∈ t.names → ∃ a ∈ t, a.name = n := by
  simp[names]

theorem names_append(hd tl : Trail):
  (hd++tl).names = hd.names++tl.names := by
  simp[names]

theorem names_cons (hd: ALit)(tl : Trail):
  Trail.names (hd::tl) = hd.name::tl.names := by
  simp[names]

theorem mem_lits_mem_names {t : Trail}{l : Lit} :
  l ∈ t.lits → l.name ∈ t.names := by
  simp[lits, names]
  intro a amem heq
  exists a
  have := congrArg Lit.name heq
  simp[ALit.name_name_lit] at this
  simp[this, amem]

theorem mem_lits_names_eq {t : Trail}{l : Lit} :
  l ∈ t.lits ∨ l.negate ∈ t.lits ↔ l.name ∈ t.names := by
  simp[lits, names]
  constructor
  case mp =>
    intro h
    cases h
    case inl lh =>
      obtain ⟨ a, amem, heq ⟩ := lh
      exists a
      constructor
      case left => exact amem
      case right => simp[←heq, ALit.name_name_lit]
    case inr rh =>
      obtain ⟨ a, amem, heq ⟩ := rh
      exists a
      constructor
      case left => exact amem
      case right =>
        have := congrArg Lit.name heq
        simp[ALit.name_name_lit, Lit.name_name_negate] at this
        exact this
  case mpr =>
    intro h
    obtain ⟨ a, amem, heq ⟩ := h
    rw[←ALit.name_name_lit] at heq
    have := Lit.shared_name heq
    cases this
    case inl lh =>
      left
      exists a
    case inr rh =>
      right
      exists a



def unseen (t : Trail)(n : Nat) : Prop := n ∉ t.names

instance : DecidableRel unseen :=
  fun t n => inferInstanceAs (Decidable (n ∉ t.names))

def wf (t : Trail) : Prop := t.names.Nodup ∧ 0 ∉ t.names

instance : DecidablePred Trail.wf := by
  intro t
  simp[wf]
  apply instDecidableAnd

theorem wf_append{hd tl : Trail}:
  (hd++tl).wf → hd.wf ∧ tl.wf := by
  simp[wf, names_append, List.nodup_append]
  intro hdNodup tlNodup nodup nozerohd nozerotl
  simp[hdNodup, tlNodup, nozerohd, nozerotl]

theorem wf_cons{hd : ALit}{tl : Trail}:
  Trail.wf (hd::tl) → tl.wf := by
  simp[wf, names_cons, List.nodup_cons]
  intro hdNodup tlNodup nozerohd nozerotl
  simp[tlNodup, nozerotl]

theorem wf_hd {hd : ALit}{tl : Trail}:
  Trail.wf (hd::tl) → hd.name ∉ tl.names := by
  intro h contra
  simp[wf, names_cons] at h
  have := h.1.1
  contradiction

theorem mem_names_comm {a : ALit}{hd tl : Trail}:
  a.name ∈ Trail.names (hd ++ tl) ↔ a.name ∈ Trail.names (tl ++ hd) := by
  simp[Trail.names]
  constructor
  all_goals
  intro h
  cases h
  case inl lh => right; exact lh
  case inr rh => left; exact rh

theorem mem_names_comm_lit {a : Lit}{hd tl : Trail}:
  a.name ∈ Trail.names (hd ++ tl) ↔ a.name ∈ Trail.names (tl ++ hd) := by
  simp[Trail.names]
  constructor
  all_goals
  intro h
  cases h
  case inl lh => right; exact lh
  case inr rh => left; exact rh
