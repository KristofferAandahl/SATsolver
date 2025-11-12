import SATsolver.Experiment.Data.Lit

inductive ALit where
  | decided : Lit → ALit
  | deduced : Lit  → ALit

namespace ALit

def lit : ALit → Lit
  | decided l => l
  | deduced l  => l

instance : Coe ALit Lit where
  coe a := a.lit

def negate : ALit → ALit
  | decided l => decided l.negate
  | deduced l  => decided l.negate

def decidedP : ALit → Prop
  | decided _ => True
  | deduced _ => False

def decidedB : ALit → Bool
  | decided _ => true
  | deduced _ => false

def deducedP : ALit → Prop
  | decided _ => False
  | deduced _ => True

def deduceB : ALit → Bool
  | decided _ => false
  | deduced _ => true

theorem decidedP_iff_decidedB (a : ALit) :
  decidedB a = true ↔ decidedP a := by
  simp[decidedP, decidedB]
  split
  all_goals simp

instance : DecidablePred decidedP :=
  fun
  | decided _ => isTrue trivial
  | deduced _ => isFalse (by simp [decidedP])

theorem dec_is_dec {a : ALit}:
    a.decidedP ↔ ∃ l, a = decided l := by
    simp[decidedP]
    split
    all_goals simp

def name : ALit → Nat
  | decided l | deduced l => l.name

theorem name_name_lit {a : ALit} :
  a.lit.name = a.name := by
  simp only [name, lit, Lit.name]
  rcases a with ⟨ l ⟩ | ⟨ l ⟩
  all_goals cases l
  all_goals simp
