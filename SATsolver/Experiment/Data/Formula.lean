import SATsolver.Experiment.Data.Clause

abbrev Formula : Type := List Clause

namespace Formula

def lits (f : Formula) : List Lit := f.flatten

def wf(f : Formula) : Prop := ∀ c ∈ f, c.wf

def mem_memClause_mem {f : Formula}{c : Clause} :
  c ∈ f → ∀ l ∈ c, l ∈ f.lits := by
  intro mem l lmem
  induction f with
  | nil => contradiction
  | cons x xs ih =>
    cases mem
    case head =>
      simp[lits]
      left; exact lmem
    case tail mem =>
      have mem : c ∈ xs := mem
      have := ih mem
      simp[lits] at ⊢ this
      right; exact this


def names (f : Formula) : List Nat := (f.flatMap Clause.names)

def names_cons {f : Formula}(wf : f.wf) :
  f ≠ [] → f.names ≠ [] := by
  intro h
  rw[List.ne_nil_iff_exists_cons] at h
  obtain ⟨ c, cs, h ⟩ := h
  subst h
  simp[names, Clause.names]
  intro falsity
  have : c ≠ [] := by
    simp[Formula.wf, Clause.wf] at wf
    simp[wf]
  contradiction


def mem_memClause_mem_names {f : Formula}{c : Clause}{n : Nat} :
  c ∈ f → n ∈ c.names → n ∈ f.names := by
  intro mem nmem
  induction f with
  | nil => contradiction
  | cons x xs ih =>
    cases mem
    case head =>
      simp[names]
      left; exact nmem
    case tail mem =>
      have mem : c ∈ xs := mem
      have := ih mem
      simp[names] at ⊢ this
      right; exact this

instance : Membership Clause Formula where
  mem f c := c ∈ f

instance : Membership Lit Formula where
  mem f l := ∃ c ∈ f, l ∈ c

end Formula

abbrev Variables : Type := Nat

namespace Variables

-- Checks that all the variables is in a formula
-- and that the formula contains all the vars
def wf (vs : Variables)(f : Formula) : Prop :=
  (∀ n ∈ f.names, n ≤ vs) ∧ (∀ n ≤ vs, n ∈ f.names)

instance : DecidableRel wf := by
  intro vs f
  simp[wf]
  exact instDecidableAnd
