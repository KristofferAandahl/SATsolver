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

theorem Formula.con_iff_exists_csCon {f : Formula}{t : Trail} :
  t ⊭ f ↔ ∃ c ∈ f, t ⊭ c := by
  simp[Conflict.con]

theorem concflict_comm {hd tl : Trail}{f : Formula} :
  hd ++ tl ⊭ f ↔ tl ++ hd ⊭ f := by
  simp[Conflict.con]
  constructor
  all_goals
    intro h
    obtain ⟨ c, cmem ,call ⟩ := h
    exists c
    simp[cmem]
    intro l lmem
    have := call l lmem
    simp[Trail.lits_append] at this ⊢
    rw[or_comm]
    exact this

theorem concflict_comm_lit{hd tl : Trail}{l : Lit} :
  hd ++ tl ⊭ l ↔ tl ++ hd ⊭ l := by
  simp[Conflict.con]
  constructor
  all_goals
    intro h
    simp[Trail.lits] at h ⊢
    rcases h with ⟨ h ⟩ | ⟨ h ⟩
    all_goals
      obtain ⟨ a, amem, ah ⟩ := h
      simp[←exists_or]
      exists a
      simp[amem, ah]
