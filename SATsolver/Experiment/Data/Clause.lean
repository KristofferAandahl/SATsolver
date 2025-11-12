import SATsolver.Experiment.Data.Trail

abbrev Clause : Type := List Lit

namespace Clause

def names (c : Clause) : List Nat := c.map Lit.name

theorem mem_mem_name {c : Clause}{l : Lit} :
  l ∈ c → l.name ∈ c.names := by
  intro mem
  simp[names]
  exists l

theorem mem_names_exist_mem {c : Clause}{n : Nat} :
  n ∈ c.names → ∃ l, l.name = n ∧ l ∈ c := by
  simp[names]
  intro l lmem lname
  exists l

def wf (c : Clause) : Prop :=
  c ≠ [] ∧ ∀ l1 ∈ c, ∀ l2 ∈ c, l1 ≠ l2 → l1.name ≠ l2.name


theorem wf_names {c : Clause} :
  c.wf → c.names ≠ [] := by
  simp[wf, names]
  intro nNil _
  exact nNil
