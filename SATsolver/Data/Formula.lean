import SATsolver.Data.Clause


abbrev Formula : Type := Array Clause

namespace Formula

def toStringHelper (str : String): List Clause → String
  | [] => str
  | c :: [] => str ++ s!"{c}"
  | c :: cs => toStringHelper (str ++ s!"{c} ⋀ ") cs

def toString (formula : Formula) : String :=
  toStringHelper "" formula.toList

end Formula

instance : ToString Formula where
  toString x := Formula.toString x

#eval ([(-1 : Int), (2 : Int)] : Clause).contains (Lit.ofInt (-1))
