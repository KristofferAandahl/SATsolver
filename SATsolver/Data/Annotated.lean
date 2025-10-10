import SATsolver.Data.Literal
import SATsolver.Data.Clause

/-
  An annotated literal is a decided literal. It is either
  decided by choice or propogated from some clause
-/

inductive AnnotatedLit where
  | decided : Lit → Nat → AnnotatedLit
  | propogated : Lit → Clause → AnnotatedLit

namespace AnnotatedLit

def toString: AnnotatedLit → String
  | decided l i => s!"{l}†[{i}]"
  | propogated l c => s!"{l}({c})"


instance : ToString AnnotatedLit where
  toString x := AnnotatedLit.toString x

def getName: AnnotatedLit → Nat
  | decided l _ => l.getName
  | propogated l _ => l.getName

def getLiteral: AnnotatedLit → Lit
  | decided l _ => l
  | propogated l _ => l

@[simp] theorem simp_getName (lit : AnnotatedLit) : lit.getLiteral.getName = lit.getName := by
  cases lit
  case decided l n =>
    simp[getLiteral, getName]
  case propogated l c =>
    simp[getLiteral, getName]

instance : BEq AnnotatedLit where
  beq a b := match a with
    | decided al an => match b with
      | decided bl bn => al == bl ∧ an == bn
      | propogated _ _ => false
    | propogated al ac => match b with
      | decided _ _ => false
      | propogated bl bc => al == bl ∧ ac == bc

instance : LawfulBEq AnnotatedLit where
  eq_of_beq := by
    intro a b h
    simp[BEq.beq] at h
    cases a <;> cases b<;> simp at h
    simp
    case decided.decided a n b m =>
      cases a <;> cases b <;> simp at h
      all_goals
       simp
       exact h
    case propogated.propogated a ac b bc =>
      cases a<;> cases b<;> simp at h
      all_goals
        let ⟨ nh, ch ⟩ := h
        have ch2 := Clause.instLawfulBEq.eq_of_beq ch
        rw[nh, ch2]
  rfl := by
    intro a
    simp[BEq.beq]
    cases a <;> simp
    case decided l n =>
      cases l <;> simp
    case propogated l c =>
      cases l <;> simp
      all_goals
      induction c with
      | nil => simp[Clause.beq]
      | cons b bs ih =>
        simp[Clause.beq]
        exact ih

end AnnotatedLit

#eval AnnotatedLit.decided (-1 : Int) 1
