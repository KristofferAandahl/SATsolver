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

def negate : AnnotatedLit → AnnotatedLit
  | decided l k => decided l.negated k
  | propogated l c => propogated l.negated c

instance : Coe AnnotatedLit Lit  where
  coe a := a.getLiteral

def isPos : AnnotatedLit → Bool
  | decided (Lit.pos _) _  => true
  | decided (Lit.neg _) _ => false
  | propogated (Lit.pos _) _ => true
  | propogated (Lit.neg _) _ => false

@[simp]
theorem simp_getName (lit : AnnotatedLit) : lit.getLiteral.getName = lit.getName := by
  cases lit
  case decided l n =>
    simp[getLiteral, getName]
  case propogated l c =>
    simp[getLiteral, getName]

theorem name_negated {a : AnnotatedLit} :
  a.getName = a.negate.getName := by
  simp[negate, ←simp_getName]
  rcases a with ⟨ l, k ⟩ | ⟨ l, c ⟩
  all_goals
    simp[getLiteral]

theorem name_ineq {a b : AnnotatedLit} :
  a.getName ≠ b.getName → a ≠ b := by
  rcases a with ⟨ al, ak ⟩ | ⟨ al, ac ⟩ <;>
  rcases b with ⟨ bl, bk ⟩ | ⟨ bl, bc ⟩
  case decided.propogated | propogated.decided => simp
  case decided.decided | propogated.propogated=>
    intro h
    simp[←simp_getName, getLiteral] at h
    rcases al with n | n <;>
    rcases bl with m | m
    case pos.neg | neg.pos => simp
    case pos.pos | neg.neg =>
      simp[Lit.getName] at h ⊢
      intro
      contradiction



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
      cases l
      all_goals
      rcases c with ⟨ c, inv ⟩
      induction c with
      | nil => simp[Clause.beq]
      | cons b bs ih =>
        simp[Clause.beq] at ih ⊢
        exact ih inv.2.2

end AnnotatedLit

#eval AnnotatedLit.decided (-1 : Int) 1
