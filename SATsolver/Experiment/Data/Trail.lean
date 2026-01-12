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

theorem mem_lits_exists_mem {t : Trail}{l : Lit} :
  l ∈ t.lits → ∃ a ∈ t, a.lit = l := by
  simp[lits]

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

theorem lit_and_litn_not_wf{l : Lit}{t : Trail} :
  l ∈ t.lits → l.negate ∈ t.lits → ¬ t.wf := by
  intro lmem lnmem
  simp[Trail.wf]
  intro nodup
  induction t
  case nil => simp[Trail.lits] at lmem
  case cons x xs ih =>
    simp[Trail.lits] at lmem lnmem
    rcases lmem <;> rcases lnmem
    case inl.inl heq1 heq2 =>
      rw[←heq2] at heq1
      simp[Lit.neg_ineq] at heq1
    case inl.inr heq hmem =>
      obtain ⟨ b, bmem, heq2 ⟩ := hmem
      simp[Trail.names] at nodup
      have hneq := nodup.1 b bmem
      have := congrArg Lit.name heq2
      simp[ALit.name_name_lit] at this
      rw[this] at hneq
      have := congrArg Lit.name heq
      simp[ALit.name_name_lit] at this
      rw[←this] at hneq
      simp[Lit.name_name_negate] at hneq
    case inr.inl hmem heq =>
      obtain ⟨ b, bmem, heq2 ⟩ := hmem
      simp[Trail.names] at nodup
      have hneq := nodup.1 b bmem
      have := congrArg Lit.name heq2
      simp[ALit.name_name_lit] at this
      rw[this] at hneq
      have := congrArg Lit.name heq
      simp[ALit.name_name_lit] at this
      rw[←this] at hneq
      simp[Lit.name_name_negate] at hneq
    case inr.inr hmem1 hmem2 =>
      simp[Trail.lits] at ih
      obtain ⟨ a, amem, heq1 ⟩ := hmem1
      obtain ⟨ b, bmem, heq2 ⟩ := hmem2
      have := ih a amem heq1 b bmem heq2 (List.nodup_cons.mp nodup).2
      simp [Trail.names] at this ⊢
      right; exact this



theorem lit_of_wf{l : Lit}{t : Trail} :
  l.name ∈ t.names → t.wf →
  l ∈ t.lits ∧ l.negate ∉ t.lits ∨ l ∉ t.lits ∧ l.negate ∈ t.lits := by
  intro namemem twf
  have := Trail.mem_lits_names_eq.mpr namemem
  cases this
  case inl lh =>
    left
    constructor
    case left => exact lh
    case right =>
      intro contra
      have := lit_and_litn_not_wf lh contra
      contradiction
  case inr rh =>
    right
    constructor
    case left =>
      intro contra
      have := lit_and_litn_not_wf contra rh
      contradiction
    case right => exact rh

theorem uniques {a b : ALit}{t : Trail} :
  t.wf → a ≠ b → a ∈ t → b ∈ t → a.name ≠ b.name := by
  intro twf hneq amem bmem
  induction t
  case nil => simp at amem
  case cons x xs ih =>
    cases amem <;> cases bmem
    case head.head =>
      contradiction
    case head.tail bmem =>
      intro contra
      have := twf.1
      simp[Trail.names, List.nodup_cons] at this
      have := this.1 b bmem
      simp[contra] at this
    case tail.head amem =>
      intro contra
      have := twf.1
      simp[Trail.names, List.nodup_cons] at this
      have := this.1 a amem
      simp[contra] at this
    case tail.tail amem bmem =>
      have : wf xs := by
        simp[Trail.wf] at twf ⊢
        constructor
        case left =>
          simp [Trail.names, List.nodup_cons] at twf ⊢
          exact twf.1.2
        case right =>
          simp[Trail.names] at twf ⊢
          exact twf.2.2
      exact ih this amem bmem


theorem nodup_wf{t : Trail} :
  t.wf → t.Nodup := by
  intro twf
  induction t
  case nil => simp
  case cons x xs ih =>
    have wfxs := wf_cons twf
    have xsnd := ih wfxs
    simp[xsnd]
    intro contra
    have := twf.1
    simp[names] at this
    have := this.1 x contra
    contradiction


def remove(t : Trail)(n : Nat): Trail :=
  t.filter (fun a => a.name != n)

theorem mem_remove_mem{t : Trail}{a : ALit}{n : Nat} :
  a ∈ t.remove n → a ∈ t := by
  simp[remove]
  intro amem neq
  exact amem

theorem wf_remove{t : Trail}{n : Nat}:
  t.wf → (t.remove n).wf := by
  intro twf
  simp[wf, names]
  constructor
  case left =>
    have : List.Sublist (List.map ALit.name (t.remove n)) (List.map ALit.name t) := by
      rw[List.sublist_map_iff]
      exists t.remove n
      simp[remove]
    exact List.Nodup.sublist this twf.1
  case right =>
    intro a amem
    simp[remove] at amem
    have zeroh := twf.2
    have := mem_mem_names amem.1
    intro contra
    rw[contra] at this
    contradiction

theorem wf_remapp{t : Trail}{a : ALit}:
  t.wf → a ∈ t → wf (t.remove a.name ++ [a]) := by
  intro twf amem
  have nodup := nodup_wf twf
  have wfr : wf (t.remove a.name) := wf_remove twf
  simp[wf, names] at *
  constructor
  case left =>
    simp[List.nodup_append, wfr]
    intro b bmem contra
    have := mem_mem_names bmem
    rw[contra] at this
    simp[names, remove] at this
    obtain ⟨ b, bh, heq⟩ := this
    simp[heq] at bh
  case right =>
    constructor
    case left => exact wfr.2
    case right =>
      intro contra
      have := twf.2 a amem
      simp[contra] at this

theorem remove_eq{t : Trail}{a b: ALit}:
  t.wf → a ∈ t → b ∈ t → a ∈ (t.remove b.name) ∨ a = b := by
  intro twf amem bmem
  simp[remove, amem]
  by_cases heq : a = b
  case pos => simp[heq]
  case neg =>
    have := uniques twf heq amem bmem
    simp[this]

theorem wfapp_wfremapp{hd tl : Trail}{a : ALit}:
  (hd++tl).wf → Trail.wf (a::tl) → ((hd.remove a.name) ++ a :: tl).wf := by
    intro twf awf
    simp[wf] at twf awf ⊢
    constructor
    case right =>
      simp[names, remove] at twf ⊢
      constructor
      case left =>
        intro x xmem hneq
        exact twf.2.1 x xmem
      case right =>
        constructor
        case left =>
          intro contra
          symm at contra
          have := awf.2
          simp[names, contra] at this
        case right =>
          intro x xmem
          exact twf.2.2 x xmem
    case left =>
      simp[names, List.nodup_append]
      constructor
      case left =>
        have : (hd.remove a.name).wf := wf_remove (wf_append twf).1
        have := this.1
        simpa [names] using this
      case right =>
        constructor
        case left =>
            simp[names, List.nodup_cons] at awf
            exact awf.1
        case right =>
          intro x xmem
          simp[remove] at xmem
          simp[xmem.2]
          intro b bmem
          simp[names, List.nodup_append] at twf
          exact twf.1.2.2 x xmem.1 b bmem


theorem remove_nonmem {t : Trail}{n : Nat}:
  n ∉ t.names → t.remove n = t := by
  intro nin
  simp[remove]
  intro a amem
  have := mem_mem_names amem
  intro contra
  rw[contra] at this
  contradiction
