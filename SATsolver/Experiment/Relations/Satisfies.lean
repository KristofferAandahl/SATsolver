import SATsolver.Experiment.Data.Formula

class Satisfies (α β : Type) where
  sat : α → β → Prop

infix:50 "⊨" => Satisfies.sat

instance : Satisfies Lit Clause where
  sat l c := l ∈ c

instance : DecidableRel (Satisfies.sat (α := Lit) (β := Clause)) :=
  fun l c => List.instDecidableMemOfLawfulBEq l c

instance : Satisfies ALit Clause where
  sat a c := a.lit ∈ c

instance : DecidableRel (Satisfies.sat (α := ALit) (β := Clause)) :=
  fun a c => List.instDecidableMemOfLawfulBEq a.lit c

theorem Clause.mem_entails {l : Lit}{c : Clause}:
  l ∈ c ↔ l ⊨ c := by simp[Satisfies.sat]

instance : Satisfies Trail Lit where
  sat t l := l ∈ t.lits

instance : DecidableRel (Satisfies.sat (α := Trail) (β := Lit)) := by
  intro t l
  simp[Satisfies.sat]
  apply List.instDecidableMemOfLawfulBEq

instance : Satisfies Trail Clause where
  sat t c := ∃ l ∈ c, t ⊨ l

instance : DecidableRel (Satisfies.sat (α := Trail) (β := Clause)) :=
  fun t c => c.decidableBEx ( t ⊨ .)

instance : Satisfies Trail Formula where
  sat t f := ∀ (c : Clause), c ∈ f → t ⊨ c

instance : DecidableRel (Satisfies.sat (α := Trail) (β := Formula)) :=
  fun t f => (f.decidableBAll (t ⊨ .))

def Formula.sat_iff_all_csSat {f : Formula}{t : Trail} :
  t ⊨ f ↔ ∀ c ∈ f, t ⊨ c := by
  simp[Satisfies.sat]
