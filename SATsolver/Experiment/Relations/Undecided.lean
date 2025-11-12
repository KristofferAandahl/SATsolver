import SATsolver.Experiment.Data.Formula
import SATsolver.Experiment.Relations.Conflicts

class Undecided (α β : Type) where
  ud : α → β → Prop

infix:50 "¿" => Undecided.ud

instance : Undecided Trail Lit where
  ud t l := l.name ∉ t.names

instance : DecidableRel (Undecided.ud (α := Trail) (β := Lit)) := by
  intro t l
  simp[Undecided.ud, Lit.name, Trail.names]
  apply List.decidableBAll

instance : Undecided Trail Clause where
  ud t c := (∃ l' ∈ c, t¿l') ∧ (∀ l ∈ c, t¿l ∨ t⊭l)

instance : DecidableRel (Undecided.ud (α := Trail) (β := Clause)) := by
  intro a b
  simp[Undecided.ud]
  apply instDecidableAnd

theorem Clause.ud_exists_lUd{c : Clause}{t : Trail} :
  t ¿ c → ∃ l ∈ c, t ¿ l := by
  simp[Undecided.ud]
  intro l lmem lunseen _
  exists l


def Clause.unit (c :Clause)(t : Trail) : Prop :=
   ∃ l' ∈ c, t¿l' ∧ ∀ l ∈ c, l ≠ l' → t ⊭ l

instance : DecidableRel Clause.unit := by
  intro c t
  simp[Clause.unit]
  apply List.decidableBEx

def Clause.getunit (c :Clause)(t : Trail)(wf : c.unit t) : Lit :=
  let lopt := c.find? (fun l => t ¿ l)
  have : lopt.isSome := by
    simp only [Clause.unit] at wf
    obtain ⟨ l, hmem, hud, cCon ⟩ := wf
    simp[lopt]
    exists l
  lopt.get this

instance : Undecided Trail Formula where
  ud t f := ∃ c ∈ f, t¿c

instance : DecidableRel (Undecided.ud (α := Trail) (β := Formula)) := by
  intro a b
  simp[Undecided.ud]
  apply List.decidableBEx


def Formula.ud_iff_exists_csUD {f : Formula}{t : Trail} :
  t ¿ f ↔ ∃ c ∈ f, t ¿ c := by
  simp[Undecided.ud]
