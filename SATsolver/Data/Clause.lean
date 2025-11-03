import Std.Data.HashSet
import SATsolver.Data.Literal
/-
  A clause is stored as a list of Literals.
  It's logical representation is a disjunction of the
  store literals
-/

def Clause.invariant (c : List Lit) : Prop :=
  match c with
  | [] => true
  | x::xs => x ∉ xs ∧ x.getName ∉ xs.map (fun lit => lit.getName) ∧ invariant xs

structure Clause where
  lits : List Lit
  inv : Clause.invariant lits

namespace Clause


def toStringHelper (str : String): List Lit → String
  | [] => str
  | l :: [] => str ++ s!"{l}"
  | l :: cs => toStringHelper (str ++ s!"{l} ∨ ") cs

def toString (c : Clause) : String :=
  toStringHelper "" c.lits

instance : ToString Clause where
  toString x := Clause.toString x

def subclause (as : Clause)(bs : Clause) : Prop :=
  ∀ a ∈ as.lits, a ∈ bs.lits

def entails (as : Clause)(bs : Clause) : Bool :=
  as.lits.all (fun a => bs.lits.contains a)

theorem entails_eq_sub (as : Clause)(bs : Clause) : as.entails bs = true ↔ as.subclause bs := by
  simp [entails, subclause]

def beq (as : Clause)(bs : Clause) : Bool :=
  match as with
  | ⟨ [], _ ⟩ => match bs with
    | ⟨ [], _ ⟩ => true
    | ⟨ _ :: _, _ ⟩  => false
  | ⟨ a :: as', inv_a ⟩ => match bs with
    | ⟨ [], _ ⟩ => false
    | ⟨ b :: bs', inv_b ⟩ => a == b ∧ Clause.beq ⟨ as', inv_a.right.right ⟩ ⟨ bs', inv_b.right.right⟩


@[simp] instance : BEq Clause where
  beq as bs := beq as bs

@[simp] instance : LawfulBEq Clause where
  rfl := by
    intro as
    rcases as with ⟨ as, inv ⟩
    induction as with
    | nil => simp[beq]
    | cons a as' ih =>
      simp[beq]
      simp at ih
      exact ih inv.2.2
  eq_of_beq := by
    intro as bs
    rcases as with ⟨ as, inv_a ⟩
    induction as generalizing bs with
    | nil =>
      rcases bs with ⟨ bs, inv_b ⟩
      cases bs
      all_goals simp[beq]
    | cons a as' ih =>
      intro h
      simp at h
      rcases bs with ⟨ bs, inv_b ⟩
      cases bs
      simp[beq] at h
      case cons b bs =>
        simp[beq] at h ⊢
        constructor
        exact h.left
        have := ih inv_a.right.right h.right
        simp at this
        exact this

end Clause
