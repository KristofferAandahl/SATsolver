import SATsolver.Data.Trail
import SATsolver.Data.Formula

structure State where
  M : Trail
  N : Formula
  U : Formula
  k : Nat
  C : Formula
