import SATsolver.Experiment.Data.Clause

abbrev Formula : Type := List Clause

namespace Formula

def lits (f : Formula) : List Lit := f.flatten


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

def wf(f : Formula) : Prop := ∀ c ∈ f, c.wf ∧ ∀ n ∈ f.names, ∀ m < n, m ∈ f.names


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

def mem_mem_names_cons {tl : Formula}{hd : Clause}{n : Nat} :
  n ∈ tl.names → n ∈ Formula.names (hd::tl):= by
  simp[names]
  intro c cmem nmem
  right
  exists c

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
  (∀ n ∈ f.names, n ≤ vs) ∧ (∀ n ≤ vs, n ≠ 0 → n ∈ f.names)

theorem f_cons_ne_zero {c : Clause}{cs : Formula}{v : Variables}{fwf : Formula.wf (c::cs)}:
  v.wf (c::cs) →  v ≠ 0 := by
  intro vwf
  simp[Formula.wf, wf, Clause.wf, Formula.names] at *
  have ⟨ cheq, call, czero⟩ := fwf.1.1
  simp[List.ne_nil_iff_exists_cons] at cheq
  obtain ⟨ l, ls, cheq ⟩ := cheq
  subst cheq
  simp[Clause.names] at czero
  have zlt : 0 < l.name := by
    have := czero.1
    rw[←Nat.ne_zero_iff_zero_lt]
    intro contra
    rw[contra] at this
    contradiction
  have lle := vwf.1 l.name (by simp[Clause.names])
  have : 0 < v := Nat.lt_of_lt_of_le zlt lle
  simp[Nat.ne_zero_iff_zero_lt, this]


instance : DecidableRel wf := by
  intro vs f
  simp[wf]
  exact instDecidableAnd


end Variables



/-
def exists_v {f : Formula}{wf : f.wf} :
  f ≠ [] → ∃ (v : Variables), v.wf f := by
  simp[Variables.wf, Formula.wf] at *
  intro h
  induction f
  case nil => contradiction
  case cons c cs csih =>
    cases cs
    case nil =>
      simp[Formula.names, Clause.wf] at *
      induction c
      case nil => simp at wf
      case cons l ls lsih =>
        cases ls
        case nil =>
          simp[Clause.names]
          exists l.name
          simp
-/
