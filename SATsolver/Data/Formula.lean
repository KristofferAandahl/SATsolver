import SATsolver.Data.Clause


abbrev Formula : Type := List Clause

namespace Formula

def wf (f : Formula) : Prop :=
  f.Nodup ∧ ∀ c ∈ f, c.lits ≠ []

def toStringHelper (str : String): List Clause → String
  | [] => str
  | c :: [] => str ++ s!"{c}"
  | c :: cs => toStringHelper (str ++ s!"{c} ⋀ ") cs

def toString (formula : Formula) : String :=
  toStringHelper "" formula

def names (f : Formula) : List Nat :=
  (f.flatMap Clause.names)

def names_no_dup (f : Formula) : List Nat := sorry

theorem names_ne_nil_f_ne_nil {f : Formula}(wf : f.wf) :
  f.names ≠ [] ↔ f ≠ [] := by
  simp [names]
  constructor
  case mp =>
    intro h contra
    obtain ⟨ c, cmem, cunseen ⟩ := h
    rw[contra] at cmem
    contradiction
  case mpr =>
    intro h
    cases f
    case nil => contradiction
    case cons c cs =>
      exists c
      simp[Clause.names]
      exact wf.2 c List.mem_cons_self



end Formula

def List.toFormula (f : List Clause) : Formula := f

instance : ToString Formula where
  toString x := Formula.toString x
