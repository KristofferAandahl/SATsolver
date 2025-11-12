import SATsolver.Experiment.Data.ALit

abbrev Trail : Type := List ALit

namespace Trail

def lits : Trail → List Lit
  | t => t.map ALit.lit

theorem mem_mem_lits{t : Trail}{a : ALit} :
  a ∈ t → a.lit ∈ t.lits := by
  simp[lits]
  intro h
  exists a

def names : Trail → List Nat
  |t => t.map ALit.name

theorem mem_name_exists_mem {t : Trail}{n : Nat} :
  n ∈ t.names → ∃ a ∈ t, a.name = n := by
  simp[names]

def unseen (t : Trail)(n : Nat) : Prop := n ∉ t.names

instance : DecidableRel unseen :=
  fun t n => inferInstanceAs (Decidable (n ∉ t.names))

def wf (t : Trail) : Prop := t.names.Nodup

instance : DecidablePred Trail.wf :=
  fun t => List.nodupDecidable (t.names)
