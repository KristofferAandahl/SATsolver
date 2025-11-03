import Std.Data.HashMap
import SATsolver.Data.Annotated

structure Trail.Entry where
  data : AnnotatedLit
  prev : Option Nat

instance : Coe Trail.Entry AnnotatedLit where
  coe a := a.data

@[simp] def Trail.invariant ( entries : Std.HashMap Nat Trail.Entry )(prev : Option Nat) : Prop :=
  ((exi : prev.isSome) → (prev.get exi) ∈ entries) ∧
  ∀ n : Nat, (h : n ∈ entries) → ∃ e : Entry, e.data.getName = n ∧ entries[n]'h = e

structure Trail where
  entries : Std.HashMap Nat Trail.Entry
  prev : Option Nat
  inv : Trail.invariant entries prev

namespace Trail

def mem (n : Nat)(as : Trail): Prop :=
  n ∈ as.entries

instance : Membership Nat Trail where
  mem as a := Trail.mem a as

def empty : Trail :=
  ⟨ {}, none, by simp ⟩

theorem mem_empty (n : Nat) : n ∉ Trail.empty := by
  simp[empty, Membership.mem]
  intro contra
  simp[mem] at contra

def emptyWithCapacity (capacity : Nat) : Trail :=
  ⟨ Std.HashMap.emptyWithCapacity capacity, none, by simp ⟩

def push (trail : Trail)(lit : AnnotatedLit)(new : lit.getName ∉ trail.entries): Trail :=
  let entry: Entry := ⟨ lit, trail.prev ⟩
  let name : Nat := lit.getName
  let entries' := trail.entries.insert name entry
  let inv' : invariant entries' (some name) := by
    simp
    constructor
    case left => simp[entries']
    case right =>
    intro n nh
    cases trail
    case mk entries prev inv =>
      simp[entries'] at nh
      cases nh
      case inl leftH => simp[←leftH, entries', entry, name]
      case inr rightH =>
        simp at inv
        have := inv.right n rightH
        simp[entries', Std.HashMap.getElem_insert]
        by_cases name = n
        case pos posH => simp[posH, entry, name]
        case neg negH => simp[negH, this]
  ⟨ entries', some name, inv' ⟩

theorem mem_push (a : AnnotatedLit)(as : Trail)(new : a.getName ∉ as.entries) :
  a.getName ∈ as.push a new := by
    simp[push, Membership.mem]
    cases as
    case mk as prev inv =>
      simp[mem]

theorem entry_unique (t : Trail)
  (n₁ n₂ : Nat)
  (h₁ : n₁ ∈ t.entries) (h₂ : n₂ ∈ t.entries)
  (eq_name : (t.entries[n₁]'h₁).data.getName = (t.entries[n₂]'h₂).data.getName) :
  t.entries[n₁]'h₁ = t.entries[n₂]'h₂ := by
  -- get witnesses from the invariant
  have ⟨e₁, he₁_name, he₁_eq⟩ := t.inv.2 n₁ h₁
  have ⟨e₂, he₂_name, he₂_eq⟩ := t.inv.2 n₂ h₂
  -- rewrite entries using these witnesses
  rw [he₁_eq, he₂_eq] at eq_name ⊢
  -- names correspond to keys
  rw [he₁_name, he₂_name] at eq_name
  -- conclude the keys are equal
  subst eq_name
  -- now same key: both sides are entries[n₁]
  simp[←he₁_eq, ←he₂_eq]


def satisfies (trail : Trail) (l : Lit) : Prop :=
  ∃ ann ∈ trail.entries.values, ann.data = l

def falsifies (trail : Trail) (l : Lit) : Prop :=
  ∃ ann ∈ trail.entries.values, ann.data = -l

def unassigned (trail : Trail) (l : Lit) : Prop :=
  l.getName ∉ trail.entries

def satisfiesB (trail : Trail) (l : Lit) : Bool :=
  match trail.entries[l.getName]? with
  | some ann => ann.data == l
  | none => false

def falsifiesB (trail : Trail) (l : Lit) : Bool :=
  match trail.entries[l.getName]? with
  | some ann => ann.data == -l
  | none => false

def unassignedB (trail : Trail) (l : Lit) : Bool :=
  (trail.entries[l.getName]?).isNone

@[simp]
theorem satisfies_iff_satisfiesB (trail : Trail) (l : Lit) : trail.satisfies l ↔ trail.satisfiesB l := by
  sorry
@[simp]
theorem falsifies_iff_falsifiesB (trail : Trail) (l : Lit) : trail.falsifies l ↔ trail.falsifiesB l := by
  sorry

@[simp]
theorem unassigned_iff_unassignedB (trail : Trail) (l : Lit) : trail.unassigned l ↔ trail.unassignedB l := by
  simp[unassigned, unassignedB]

end Trail
