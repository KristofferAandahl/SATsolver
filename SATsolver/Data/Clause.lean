import Std.Data.HashSet
import SATsolver.Data.Literal
/-
  A clause is stored as an array of Literals.
  It's logical representation is a disjunction of the
  store literals
-/
abbrev Clause : Type := List Lit

namespace Clause

def toStringHelper (str : String): List Lit → String
  | [] => str
  | l :: [] => str ++ s!"{l}"
  | l :: cs => toStringHelper (str ++ s!"{l} ∨ ") cs

def toString (c : Clause) : String :=
  toStringHelper "" c

instance : ToString Clause where
  toString x := Clause.toString x

instance : Coe (List Lit) Clause where
  coe x := (x : Clause)

def subclause (as : Clause)(bs : Clause) : Prop :=
  ∀ a ∈ as, a ∈ bs

def entails (as : Clause)(bs : Clause) : Bool :=
  as.all (fun a => bs.contains a)

theorem entails_eq_sub (as : Clause)(bs : Clause) : as.entails bs = true ↔ as.subclause bs := by
  simp [entails, subclause]

def beq (as : Clause)(bs : Clause) : Bool :=
  match as with
  | [] => match bs with
    | [] => true
    | _ :: _ => false
  | a :: as' => match bs with
    | [] => false
    | b :: bs' => a == b ∧ Clause.beq as' bs'

@[simp] instance : BEq Clause where
  beq as bs := beq as bs

@[simp] instance : LawfulBEq Clause where
  rfl := by
    intro as
    induction as with
    | nil => simp[beq]
    | cons a as' ih =>
      simp[beq]
      simp at ih
      exact ih
  eq_of_beq := by
    intro as bs
    induction as generalizing bs with
    | nil =>
      cases bs <;> simp[beq]
    | cons a as' ih =>
      cases bs <;> simp[beq]
      case cons.cons b bs' =>
        intro lit_h list_h
        have tail_eq : as' = bs' := ih list_h
        exact And.intro lit_h tail_eq

end Clause
