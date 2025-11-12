import SATsolver.Data.ListTrail
import SATsolver.Entailment

inductive Status where
  | sat : Status
  | fals : Status
  | undecided : Status



namespace Trail
/-
This file contains interactions between a trail of annotated literals and literals.
They are used to check whether or not a literal is undecided, satisfied or falsified by a trail.
-/
def satisfies (t : Trail)(l : Lit) : Prop :=
  ∃ a ∈ t.trail, a.getLiteral = l

instance: Entails Trail Lit where
  entails t l := t.satisfies l

def satisfiesB (t : Trail)(l : Lit) :=
  match t.get? l with
  | none => false
  | some a => a.getLiteral = l

def falsifies (t : Trail)(l : Lit) : Prop :=
  ∃ a ∈ t.trail, a.getLiteral = -l

def falsifiesB (t : Trail)(l : Lit) :=
  match t.get? l with
  | none => false
  | some a => a.getLiteral = -l

def undecided (t : Trail)(l : Lit) : Prop :=
  l.getName ∉ t.names

def undecidedB (t : Trail)(l : Lit) :=
  match t.get? l with
  | none => true
  | some _ => false

def decided (t : Trail)(l: Lit) : Prop :=
  l.getName ∈ t.names

def decidedB (t : Trail)(l : Lit) :=
  match t.get? l with
  | none => false
  | some _ => true


@[simp]
theorem satisfies_iff_satisfiesB (t : Trail)(l : Lit) :
  t.satisfiesB l = t.satisfies l := by
  simp[satisfies, satisfiesB]
  constructor
  case mp =>
    intro h; split at h;
    case h_1 => contradiction
    case h_2 oe a hget =>
      simp at h
      subst h
      exists a
      simp
      exact (get?_eq_some_iff_mem t a).mp hget
  case mpr =>
    intro h; cases h;
    case intro a ah =>
      have := get?_mems_lit t a ah.left
      rw[ah.right] at this
      simp[this, ah.right]

theorem satisfies_not_empty (t : Trail)(l : Lit) :
  t.satisfies l → t.trail ≠ [] := by
  simp[satisfies]
  intro a a_mem h_al
  exact List.ne_nil_of_mem a_mem

theorem satisfies_subset_satisfies (t : Trail)(l : Lit) :
  ∀ t', t' ⊆ t → t'.satisfies l → t.satisfies l := by
  simp[Trail.satisfies]
  intro t' t'ss a a_mem_t' h_al
  exists a
  constructor
  exact Trail.mem_mem_subset t a t' t'ss a_mem_t'
  exact h_al

@[simp]
theorem falsifies_iff_falsifiesB (t : Trail)(l : Lit) :
  t.falsifiesB l = t.falsifies l := by
  simp[falsifies, falsifiesB]
  constructor
  case mp =>
    intro h; split at h;
    case h_1 => contradiction
    case h_2 oe a hget =>
      simp at h
      rw[←get?_eq_get?_neg, ←h] at hget
      exists a
      constructor
      exact (get?_eq_some_iff_mem t a).mp hget
      exact h
  case mpr =>
    intro h; cases h;
    case intro a ah =>
    have := get?_mems_lit t a ah.left
    simp[ah.right] at this
    simp[this, ah.right]

theorem falsifies_subset_falsifies {t t' : Trail}{l : Lit} :
  t' ⊆ t → t'.falsifies l → t.falsifies l := by
  simp[Trail.falsifies]
  intro t'ss a a_mem_t' h_al
  exists a
  constructor
  exact Trail.mem_mem_subset t a t' t'ss a_mem_t'
  exact h_al

theorem satisfies_ne_falsifies {t : Trail}{l : Lit}:
  t.satisfies l → ¬t.falsifies l := by
  simp[satisfies, falsifies]
  intro a a_mem h_al x x_mem h_xl
  have h_al_name := congrArg Lit.getName h_al
  have h_xl_name := congrArg Lit.getName h_xl
  simp [AnnotatedLit.simp_getName, Neg.neg, Lit.name_of_neg] at h_al_name h_xl_name
  rw[←h_al_name] at h_xl_name
  have := Trail.mem_same_name t x a x_mem a_mem h_xl_name
  subst this
  subst h_al
  exact Lit.neg_ineq x.getLiteral h_xl


@[simp]
theorem undecided_iff_undecidedB (t : Trail)(l : Lit) :
  t.undecidedB l = t.undecided l := by
  simp[undecided, undecidedB]
  constructor
  case mp =>
    intro h; split at h;
    case h_2 => contradiction
    case h_1 oe h2 =>
      simp[←get?_some_iff_mem_names, h2]
  case mpr =>
    intro h
    simp[←get?_some_iff_mem_names] at h
    rw[h]

@[simp]
theorem decided_iff_decidedB (t : Trail)(l : Lit) :
  t.decidedB l = t.decided l := by
    simp[decided, decidedB]
    constructor
    case mp =>
      intro h; split at h;
      case h_1 => contradiction
      case h_2 oe a h2 =>
        simp[←get?_some_iff_mem_names, congrArg Option.isSome h2]
    case mpr =>
      intro h
      simp[←get?_some_iff_mem_names] at h
      split
      case h_1 oe noneH =>
        -- Creates a contradiction
        rw[noneH] at h
        simp at h
      case h_2 oe someH =>
        simp

@[simp]
theorem decided_iff_not_undecided{t : Trail}{l : Lit}:
  ¬t.undecided l ↔ t.decided l:= by
  simp[undecided, decided]

theorem not_decided_iff_undecided{t : Trail}{l : Lit}:
  t.undecided l ↔ ¬t.decided l:= by
  simp[undecided, decided]

@[simp]
theorem decided_iff_sat_or_falsifed {t : Trail}{l : Lit} :
  t.satisfies l ∨ t.falsifies l ↔ t.decided l  := by
  simp[decided, satisfies, falsifies]
  constructor
  case mp =>
    intro h
    cases h
    case inl satH =>
      rcases satH with ⟨ a, ⟨ a_mem, a_lit_eq ⟩ ⟩
      have := t.mem_mem_names a a_mem
      rw[←a.simp_getName, a_lit_eq] at this
      exact this
    case inr falsiH =>
      rcases falsiH with ⟨ a, ⟨ a_mem, a_lit_neq ⟩ ⟩
      have := t.mem_mem_names a a_mem
      rw[←a.simp_getName, a_lit_neq] at this
      simp[Neg.neg, l.name_of_neg] at this
      exact this
  case mpr =>
    intro h
    obtain ⟨ a, ⟨ a_mem, aName_eq ⟩ ⟩ := t.names_exi_mem l.getName h
    rw[←AnnotatedLit.simp_getName] at aName_eq
    have a_lit := Lit.same_name a.getLiteral l aName_eq
    cases a_lit
    case inl aLit_eq => left; exists a;
    case inr aLit_neq => right; exists a;

theorem sat_iff_not_false_or_u (t : Trail)(l : Lit) :
  t.satisfies l ↔ ¬t.falsifies l ∧ ¬ t.undecided l := by
  constructor
  case mp =>
    simp[satisfies, falsifies, undecided]
    cases t
    case mk t inv =>
    induction t with
    | nil => simp
    | cons x xs ih =>
      intro a a_mem a_l
      constructor
      case left =>
        intro b b_mem
        simp at *
        simp[invariant] at inv
        cases a_mem; cases b_mem;
        case inl.inl a_eq b_eq =>
          rw[b_eq, ←a_eq, a_l]
          exact Lit.neg_ineq l
        case inl.inr a_eq b_mem =>
          rw[←a_eq] at inv
          have := inv.right.left b b_mem
          intro contra
          apply this
          rw[←a_l] at contra
          have := congrArg Lit.getName contra
          simp[Neg.neg] at this
          exact this
        cases b_mem;
        case inr.inl a_mem b_eq =>
          rw[←b_eq] at inv
          have := inv.right.left a a_mem
          intro contra
          apply this
          rw[←a_l] at contra
          have := congrArg Lit.getName contra
          simp[Neg.neg] at this
          simp[this]
        case inr.inr a_mem b_mem =>
          exact (ih inv.right.right a a_mem a_l).left b b_mem
      case right =>
        simp[names] at *
        rw[←a_l]
        cases a_mem
        case inl a_eq => left; simp; exact congrArg AnnotatedLit.getName a_eq
        case inr a_mem =>
          right; exists a; constructor
          exact a_mem
          simp
  case mpr =>
    simp[←decided_iff_sat_or_falsifed]
    intro not_fals undecided
    cases undecided
    case inl sat => exact sat
    case inr sat => contradiction

theorem false_iff_not_sat_or_u {t : Trail}{l : Lit} :
  t.falsifies l ↔ ¬t.satisfies l ∧ ¬t.undecided l := by
  simp[←decided_iff_sat_or_falsifed]
  constructor
  case mp =>
    intro fals
    constructor
    case right => right; exact fals
    case left =>
       simp[sat_iff_not_false_or_u]
       intro h
       contradiction
  case mpr =>
    intro ⟨ not_sat, undecided ⟩
    cases undecided
    case inl => contradiction
    case inr fals => exact fals

end Trail

namespace Clause

def satisfiedBy(c :Clause)(t : Trail) :=
  ∃ l ∈ c.lits, t.satisfies l

def satisfiedByB(c :Clause)(t : Trail) :=
  c.lits.any (t.satisfiesB .)

@[simp]
theorem satisfies_iff_satisfiesB (c : Clause)(t : Trail) :
  c.satisfiedByB t ↔ c.satisfiedBy t := by
  simp[satisfiedBy, satisfiedByB]


def falsifiedBy( c :Clause)(t : Trail) :=
  ∀ l ∈ c.lits, t.falsifies l

def falsifiedByB( c :Clause)(t : Trail) :=
  c.lits.all (t.falsifiesB .)

@[simp]
theorem falsifies_iff_falsifiesB (c : Clause)(t : Trail):
  c.falsifiedByB t ↔ c.falsifiedBy t := by
  simp[falsifiedBy, falsifiedByB]

theorem sat_neq_fals {c : Clause}{t : Trail}:
  c.satisfiedBy t → ¬ c.falsifiedBy t := by
  simp[satisfiedBy, falsifiedBy]
  intro l l_mem l_sat
  exists l
  constructor
  exact l_mem
  exact Trail.satisfies_ne_falsifies l_sat

def undecidedBy (c : Clause)(t : Trail) :=
  (∃ l ∈ c.lits, t.undecided l) ∧ (∀ l ∈ c.lits, t.undecided l ∨ t.falsifies l)

def undecidedByB (c : Clause)(t : Trail): Bool :=
  c.lits.any (t.undecidedB .) ∧ c.lits.all (fun l => t.undecidedB l ∨ t.falsifiesB l)

def decidedBy (c : Clause)(t : Trail) :=
  c.falsifiedBy t ∨ c.satisfiedBy t

theorem undecided_if_not_decided {c : Clause}{t : Trail} :
  ¬c.decidedBy t → c.undecidedBy t := by
  simp[decidedBy, undecidedBy, satisfiedBy, falsifiedBy]
  intro l lmem nFals not_sat_h
  have nSat := not_sat_h l lmem
  have nDec : ¬t.decided l := by
    have nFS := And.intro nFals nSat
    have : ¬ (t.satisfies l∨ t.falsifies l) := by
      intro contra
      cases contra
      case inl h => simp[h] at nFS
      case inr h => simp[h] at nFS
    intro contra
    simp[←Trail.decided_iff_sat_or_falsifed] at contra
    contradiction
  constructor
  case left =>
    exists l
  case right =>
    intro k kmem
    have := not_sat_h k kmem
    simp[Trail.sat_iff_not_false_or_u] at this
    by_cases fals : t.falsifies k
    right; exact fals
    have := this fals
    simp[←Trail.decided_iff_not_undecided] at this
    left; exact this

theorem not_decided_if_undecided {c : Clause}{t : Trail} :
  c.undecidedBy t → ¬c.decidedBy t := by
  simp[decidedBy, undecidedBy, satisfiedBy, falsifiedBy]
  intro l lmem lu cu
  constructor
  case left =>
    simp[Trail.not_decided_iff_undecided, ←Trail.decided_iff_sat_or_falsifed] at lu
    exists l
    simp[lmem, lu]
  case right =>
    simp[Trail.sat_iff_not_false_or_u]
    intro k kmem knf
    have : t.undecided k ∨ t.falsifies k := cu k kmem
    simp[knf, Trail.not_decided_iff_undecided] at this
    exact this

def status (c : Clause)(t : Trail) : Status :=
  if c.satisfiedByB t then Status.sat
  else if c.falsifiedByB t then Status.fals
  else Status.undecided

@[simp]
theorem undecided_iff_undecidedB(c : Clause)(t : Trail):
  c.undecidedByB t ↔ c.undecidedBy t := by
  simp[undecidedBy, undecidedByB]

def unitBy (c : Clause)(t : Trail) :=
  ∃ l ∈ c.lits, t.undecided l ∧ ∀ k ∈ c.lits, k ≠ l → t.falsifies k


def unitByB (c : Clause)(t : Trail) :=
  let l := c.lits.find? (t.undecidedB .)
  match l with
  | none => false
  | some l => c.lits.all (fun k => k == l ∨ t.falsifiesB k)

@[simp]
theorem unit_iff_unitBy {c : Clause}{t : Trail}:
  c.unitByB t ↔ c.unitBy t := by
  simp[unitBy, unitByB]
  constructor
  case mp =>
    intro h
    split at h
    contradiction
    case h_2 oe l l_find =>
      simp[List.find?_eq_some_iff_getElem] at *
      exists l
      obtain ⟨i, i_wf, l_ind, pre_decided⟩ := l_find.2
      constructor
      exact List.mem_of_getElem l_ind
      constructor
      exact l_find.1
      intro k k_mem k_neq
      exact Or.resolve_left (h k k_mem) k_neq
  case mpr =>
    intro h
    rcases h with ⟨ l, l_mem, l_undecided, mem_h ⟩
    split
    case h_1 oe case_h =>
      simp[Trail.undecided] at case_h l_undecided
      have := case_h l l_mem
      contradiction
    case h_2 oe k k_h =>
      simp[List.find?_eq_some_iff_getElem] at *
      obtain ⟨i, i_wf, k_ind, pre_decided⟩ := k_h.2
      by_cases k_eq : k = l
      case pos =>
        subst k_eq
        intro x x_mem
        have := mem_h x x_mem
        by_cases x_eq :x=k
        left; exact x_eq
        right; exact this x_eq
      case neg =>
        have k_mem := List.mem_of_getElem k_ind
        have := mem_h k k_mem k_eq
        simp[t.false_iff_not_sat_or_u] at this
        have k_decided := this.2
        have k_undecided := k_h.1
        contradiction

theorem undecided_if_unit (c : Clause)(t : Trail):
  c.unitBy t → c.undecidedBy t := by
  simp[unitBy, undecidedBy]
  intro l l_mem l_undecided mems_decided
  constructor
  exists l
  intro k k_mem
  have k_fals := mems_decided k k_mem
  by_cases k_eq : k = l
  case pos =>
    subst k_eq
    left; exact l_undecided
  case neg =>
    right; exact k_fals k_eq

theorem fals_subset_fals {c : Clause}{t t' : Trail}:
  t ⊆ t' → c.falsifiedBy t → c.falsifiedBy t' := by
  simp[falsifiedBy]
  intro ss h l l_mem
  have : t.falsifies l := h l l_mem
  exact Trail.falsifies_subset_falsifies ss this

theorem undecided_trail_incomplete {c : Clause}{t : Trail}:
  c.undecidedBy t → ∃ n ∈ c.names, n ∉ t.names := by
  simp[undecidedBy, Trail.undecided]
  intro l hmem hlu h
  exists l.getName
  constructor
  case left =>
    simp[names]
    exists l
  case right =>
    exact hlu

theorem u_or_sat_not_fals {c : Clause}{t : Trail} :
  c.undecidedBy t ∨ c.satisfiedBy t → ¬c.falsifiedBy t := by
  simp[falsifiedBy, satisfiedBy, undecidedBy, Trail.false_iff_not_sat_or_u]
  intro h
  cases h
  case inl u =>
    obtain ⟨ l, lmem, lu ⟩ := u.left
    exists l
    constructor
    case left => exact lmem
    case right => intro; simp[←Trail.decided_iff_not_undecided, lu]
  case inr sat =>
    obtain ⟨ l, lmem, lsat ⟩ := sat
    exists l
    constructor
    case left => exact lmem
    case right => intro; contradiction

theorem not_fals_u_or_sat {c : Clause}{t : Trail}:
  c.falsifiedBy t → ¬(c.undecidedBy t ∨ c.satisfiedBy t) := by
  simp[falsifiedBy, satisfiedBy, undecidedBy]
  intro hf
  constructor
  case left =>
    intro l lmem hlu
    have : t.falsifies l := hf l lmem
    have : t.decided l := Trail.decided_iff_sat_or_falsifed.mp (Or.inr this)
    contradiction
  case right =>
    intro l lmem hlsat
    have : t.falsifies l := hf l lmem
    have := Trail.satisfies_ne_falsifies hlsat
    contradiction

theorem not_u_or_sat_fals {c : Clause}{t : Trail}:
  ¬(c.undecidedBy t ∨ c.satisfiedBy t) → c.falsifiedBy t := by
  simp[falsifiedBy, satisfiedBy, undecidedBy]
  intro hu hsat l lmem
  have hnsat : ¬t.satisfies l := hsat l lmem
  simp[Trail.sat_iff_not_false_or_u] at hnsat
  by_cases hf : t.falsifies l
  case pos => exact hf
  case neg =>
    have hlu : t.undecided l := hnsat hf
    have := hu l lmem hlu
    obtain ⟨ k, kmem, kd, knf ⟩ := this
    simp[←Trail.decided_iff_sat_or_falsifed] at kd
    cases kd
    case inl hsk =>
      have : ¬t.satisfies k := hsat k kmem
      contradiction
    case inr hsf =>
      contradiction

theorem fals_iff_not_sat_or_u {c : Clause}{t : Trail}:
  c.falsifiedBy t ↔ ¬(c.undecidedBy t ∨ c.satisfiedBy t)  := by
  constructor
  exact not_fals_u_or_sat
  exact not_u_or_sat_fals

theorem all_asssigned_decided {c : Clause}{t : Trail}:
  (∀ n ∈ c.names, n ∈ t.names) → ¬c.undecidedBy t := by
  simp [undecidedBy, Trail.undecided]
  intro h l lmem lu
  have nmem : l.getName ∈ c.names := by
    simp[names]
    exists l
  have : l.getName ∈ t.names := h l.getName nmem
  contradiction

end Clause

namespace Formula
def satisfiedBy (f : Formula)(t : Trail) : Prop :=
  (∀ c ∈ f, c.satisfiedBy t)

def is_satisfiedBy (f : Formula)(t : Trail) : Bool :=
  f.all (fun c => c.satisfiedByB t)

@[simp]
theorem satisfiedBy_iff_is_satisfiedBy (f : Formula)(t : Trail) :
  f.is_satisfiedBy t ↔ f.satisfiedBy t := by
  simp[satisfiedBy, is_satisfiedBy]

def falsifiedBy (f : Formula)(t : Trail) : Prop :=
  (∃ c ∈ f, c.falsifiedBy t)

def is_falsifiedBy (f : Formula)(t : Trail) : Bool :=
  f.any (Clause.falsifiedByB . t)

@[simp]
theorem falsifiedBy_iff_is_falsifiedBy (f : Formula)(t : Trail) :
  f.is_falsifiedBy t ↔ f.falsifiedBy t := by
  simp[falsifiedBy, is_falsifiedBy]

def decidedBy (f : Formula)(t : Trail) : Prop :=
  f.falsifiedBy t ∨ f.satisfiedBy t

theorem decided_head_sat (c : Clause)(cs : Formula)(t : Trail) :
  c.satisfiedBy t → (c::cs).toFormula.decidedBy t → cs.decidedBy t := by
  simp[List.toFormula, decidedBy, falsifiedBy, satisfiedBy]
  intro c_sat h_dec
  cases h_dec
  case inl h_fals =>
    left
    exact Or.resolve_left h_fals (Clause.sat_neq_fals c_sat)
  case inr h_sat =>
    right
    exact h_sat.right

theorem decided_parts {c : Clause}{cs : Formula}{t : Trail} :
  c.satisfiedBy t → cs.decidedBy t → (c::cs).toFormula.decidedBy t  := by
  simp[List.toFormula, decidedBy, falsifiedBy, satisfiedBy]
  intro c_sat cs_dec
  cases cs_dec
  case inl h_fals =>
    left
    right
    exact h_fals
  case inr h_sat =>
    right
    constructor
    exact c_sat
    exact h_sat


def is_decidedBy (f : Formula)(t : Trail) : Bool :=
   f.is_falsifiedBy t ∨ f.is_satisfiedBy t

@[simp]
theorem decidedBy_iff_is_decidedBy (f : Formula)(t : Trail) :
  f.is_decidedBy t ↔ f.decidedBy t := by
  simp[is_decidedBy, decidedBy]

def undecidedBy (f : Formula)(t : Trail) : Prop :=
  (∃ c ∈ f, c.undecidedBy t) ∧ ∀ c ∈ f, c.undecidedBy t ∨ c.satisfiedBy t

def is_undecidedBy (f : Formula)(t : Trail) : Bool :=
   ¬ (f.is_falsifiedBy t ∧ f.is_satisfiedBy t)

theorem fals_subset_fals {f : Formula}{t : Trail}{t' : Trail} :
  t ⊆ t' → f.falsifiedBy t → f.falsifiedBy t' := by
  simp[falsifiedBy]
  intro ss c c_mem c_fals
  exists c
  constructor
  exact c_mem
  exact Clause.fals_subset_fals ss c_fals


theorem undecided_trail_incomplete {f : Formula}{t : Trail}:
  f.undecidedBy t → f ≠ [] → ∃ n ∈ f.names, n ∉ t.names := by
  intro h wf
  simp[undecidedBy] at h ⊢
  cases f with
  | nil => simp at wf
  | cons x xs =>
    obtain ⟨ c, cmem, c_und ⟩ := h.1
    have := Clause.undecided_trail_incomplete c_und
    simp[names]
    obtain ⟨ n, nmem, n_und ⟩ := this
    exists n
    constructor
    case right => exact n_und
    case left =>
      simp at cmem
      rcases cmem with heq | hmem
      case inl =>
        left; simp[←heq, nmem]
      case inr =>
        right; exists c
