import SATsolver.Data.Clause


abbrev Formula : Type := List Clause

namespace Formula

def toStringHelper (str : String): List Clause → String
  | [] => str
  | c :: [] => str ++ s!"{c}"
  | c :: cs => toStringHelper (str ++ s!"{c} ⋀ ") cs

def toString (formula : Formula) : String :=
  toStringHelper "" formula

end Formula

def List.toFormula (f : List Clause) : Formula := f

instance : ToString Formula where
  toString x := Formula.toString x
