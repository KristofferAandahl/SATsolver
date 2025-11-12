inductive Lit where
  | pos : Nat → Lit
  | neg : Nat → Lit

namespace Lit

instance : BEq Lit where
  beq x y := match x, y with
    | pos x, pos y => x == y
    | neg x, neg y => x == y
    | _, _ => false

instance : LawfulBEq Lit where
  rfl := by
    intro a
    simp[BEq.beq]
    cases a
    all_goals simp
  eq_of_beq := by
    intro a b h
    simp[BEq.beq] at h
    cases a <;> cases b
    case pos.pos | neg.neg =>
      simp at h
      simp[h]
    case pos.neg | neg.pos =>
      simp at h

instance : DecidableEq Lit := by
  intro a b
  cases a <;> cases b
  case pos.pos a b | neg.neg a b =>
    simp
    exact Nat.decEq a b
  all_goals
    exact isFalse (by intro h; cases h)


def negate : Lit → Lit
  | pos n => neg n
  | neg n => pos n

def name : Lit → Nat
  | pos n | neg n => n

theorem name_name_negate {l : Lit} :
  l.negate.name = l.name := by
  simp[negate, name]
  cases l
  all_goals simp

theorem shared_name {a b : Lit} :
  a.name = b.name → a = b ∨ a = b.negate := by
  simp[name]
  intro h
  cases a <;> cases b
  all_goals simp[h, negate]
