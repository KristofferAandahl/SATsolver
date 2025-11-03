/-
  A Literal is an undecided boolean with a name
  based on a Natural number
-/

inductive Lit where
  | pos : Nat → Lit
  | neg : Nat → Lit
  deriving DecidableEq, Hashable

namespace Lit

def ofInt : Int → Lit
  | Int.ofNat n => Lit.pos n
  | Int.negSucc n => Lit.neg (n + 1)

instance : Coe Int Lit where
  coe x := Lit.ofInt x

def toString: Lit → String
  | Lit.pos n => s!"{n}"
  | Lit.neg n => s!"¬{n}"

instance : ToString Lit where
  toString x := Lit.toString x

def getName : Lit → Nat
  | pos n => n
  | neg n => n

def negated : Lit → Lit
  | pos n => neg n
  | neg n => pos n

instance : Neg Lit where
  neg x := Lit.negated x

instance : BEq Lit where
  beq a b := match a with
    | pos n => match b with
      | pos m => n == m
      | neg _ => false
    |neg n => match b with
      | pos _ => false
      | neg m => n == m

instance : LawfulBEq Lit where
  eq_of_beq := by
    intro a b h
    cases a with
      | pos n => cases b with
        | pos m =>
          simp[BEq.beq] at h
          rw[h]
        | neg m => simp[BEq.beq] at h
      | neg n => cases b with
        | pos m => simp[BEq.beq] at h
        | neg m =>
          simp[BEq.beq] at h
          rw[h]
  rfl := by
    intro a
    cases a
    all_goals simp[BEq.beq]

theorem neg_negated{l : Lit} :
  -l = l.negated := by
    simp[Neg.neg]

@[simp]
theorem neg_neg (l : Lit) :
  - - l = l := by
  cases l
  all_goals
    simp[Neg.neg, negated]

theorem neg_ineq (l : Lit) :
  ¬ l = -l := by
  intro contra
  cases l
  case pos n =>
    have : pos n = neg n := contra
    simp at this
  case neg n =>
    have : neg n = pos n := contra
    simp at this

theorem name_eq_neq_ineq(a b : Lit)(wf : a.getName = b.getName):
  ¬a=-b → a = b := by
  intro h
  cases a
  case pos n =>
    cases b
    case pos m => simp[getName] at wf; simp[wf]
    case neg m =>
      simp[getName] at wf;
      simp[wf, Neg.neg] at h;
      rw[negated] at h
      contradiction
  case neg n =>
    cases b
    case pos m =>
      simp[getName] at wf;
      simp[wf, Neg.neg] at h;
      rw[negated] at h
      contradiction
    case neg m => simp[getName] at wf; simp[wf]

theorem diffNameNEQ (x : Lit)(y : Lit) : x.getName ≠ y.getName → x ≠ y := by
  simp
  intro h contra
  rw[contra] at h
  exact h rfl

theorem same_name(x : Lit)(y : Lit)(wf : x.getName = y.getName) :
  x = y ∨ x = -y := by
  cases x <;> cases y <;> simp[getName, Neg.neg] at *
  case pos.pos | neg.neg => left; exact wf
  case pos.neg | neg.pos => rw[negated, wf];


@[simp] theorem name_of_neg (x : Lit) : x.negated.getName = x.getName := by
  cases x
  case pos n =>
    simp[getName, negated]
  case neg n =>
    simp[getName, negated]

theorem neg_neq (x : Lit) : x.negated ≠ x := by
  cases x
  case pos n =>
    intro contra
    cases contra
  case neg n =>
    intro contra
    cases contra

end Lit
