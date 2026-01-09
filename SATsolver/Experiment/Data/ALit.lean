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
  | deduced l  => deduced l.negate

theorem negneg {a : ALit} :
  a.negate.negate = a := by
  simp[negate]
  split
  case h_1 x l heq =>
    split at heq
    case h_1 x1 l1 =>
      simp at heq
      simp[←heq, Lit.negneg]
    case h_2 x1 l1 =>
      simp at heq
  case h_2 x l heq =>
    split at heq
    case h_1 x1 l1 =>
      simp at heq
    case h_2 =>
      simp at heq
      simp[←heq, Lit.negneg]


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

theorem ded_iff_not_dec {a : ALit} :
  a.deducedP ↔ ¬ a.decidedP := by
  simp[decidedP, deducedP]
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

theorem name_name_negate {a : ALit} :
  a.negate.name = a.name := by
  simp[name, negate]
  cases a
  all_goals simp[Lit.name_name_negate]

theorem lit_negate_negate_lit {a : ALit} :
  a.negate.lit = a.lit.negate := by
  simp[ALit.negate, ALit.lit, Lit.negate]
  cases a
  all_goals simp

theorem negation_comm {l : Lit}:
  (ALit.decided l).negate = ALit.decided (l.negate) := by
  simp[ALit.negate]

instance : BEq ALit where
  beq x y := match x, y with
    | decided x, decided y => x == y
    | deduced x, deduced y => x == y
    | _, _ => false

instance : LawfulBEq ALit where
  rfl := by
    intro a
    simp only[BEq.beq]
    cases a
    case decided l =>
      cases l
      all_goals simp
    case deduced l =>
      cases l
      all_goals simp
  eq_of_beq := by
    intro a b
    simp only [BEq.beq]
    cases a <;> cases b
    case decided.decided j k =>
      cases j <;> cases k
      all_goals simp
    case deduced.deduced j k =>
      cases j <;> cases k
      all_goals simp
    all_goals simp
