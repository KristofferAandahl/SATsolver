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
    simp only [BEq.beq]
    cases a
    all_goals simp
  eq_of_beq := by
    intro a b h
    simp only [BEq.beq] at h
    cases a <;> cases b
    case pos.pos | neg.neg =>
      simpa using h
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

theorem negneg (l : Lit) :
  l.negate.negate = l := by
  simp[negate]
  split
  case h_1 x n heq =>
    split at heq
    case h_1 k m =>
      have := congrArg negate heq
      simp[negate] at this
    case h_2 k m =>
      have := congrArg negate heq
      simp[negate] at this
      rw[this]
  case h_2 x n heq =>
    split at heq
    case h_1 k m =>
      have := congrArg negate heq
      simp[negate] at this
      rw[this]
    case h_2 k m =>
      have := congrArg negate heq
      simp[negate] at this

theorem neg_elim {l j : Lit}:
  l.negate = j.negate ↔ l = j := by
  simp[negate]
  cases l <;> cases j
  all_goals simp

def name : Lit → Nat
  | pos n | neg n => n

theorem name_name_negate {l : Lit} :
  l.negate.name = l.name := by
  simp only [negate, name]
  cases l
  all_goals simp

theorem shared_name {a b : Lit} :
  a.name = b.name → a = b ∨ a = b.negate := by
  simp only [name]
  intro h
  cases a <;> cases b
  all_goals simp[h, negate]

theorem neg_ineq{l : Lit} :
  l ≠ l.negate := by
  simp[negate]
  cases l
  all_goals simp
