import SATsolver.Data

class Entails (α β : Type) where
  entails : α → β → Prop

infix:50 "⊨" => Entails.entails
infix:50 "⊭" => ¬Entails.entails

instance : Entails Lit Clause where
  entails l c := l ∈ c.lits

instance : Entails AnnotatedLit Clause where
  entails al c := al.getLiteral ∈ c.lits

instance : Entails Trail Clause where
  entails tl c := ∃ al ∈ tl, al ⊨ c

instance : Entails Trail Formula where
  entails tl f := ∀ c ∈ f, tl ⊨ c
