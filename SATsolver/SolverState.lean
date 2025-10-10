import SATsolver.Data.Tail
import SATsolver.Data.Clause

structure State where
  M : Tail
  N : Formula
  U : Formula
  k : Nat
  C : Formula
