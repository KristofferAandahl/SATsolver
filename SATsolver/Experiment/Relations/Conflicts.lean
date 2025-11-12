import SATsolver.Experiment.Data.Formula

class Conflict (α β : Type) where
  con : α → β → Prop

infix:50 "⊭" => Conflict.con

instance : Conflict Trail Lit where
  con t l := l.negate ∈ t.lits

instance : DecidableRel (Conflict.con (α := Trail) (β := Lit)) := by
  intro t l
  simp[Conflict.con]
  apply List.instDecidableMemOfLawfulBEq

instance : Conflict Trail Clause where
  con t c := ∀ l ∈ c, t ⊭ l

instance : DecidableRel (Conflict.con (α := Trail) (β := Clause)) := by
    intro t c
    simp[Conflict.con]
    apply List.decidableBAll

instance : Conflict Trail Formula where
  con t f := ∃ c ∈ f, t ⊭ c

instance : DecidableRel (Conflict.con (α := Trail) (β := Formula)) := by
  intro t f
  simp[Conflict.con]
  apply List.decidableBEx

def Formula.con_iff_exists_csCon {f : Formula}{t : Trail} :
  t ⊭ f ↔ ∃ c ∈ f, t ⊭ c := by
  simp[Conflict.con]
