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


theorem sat_remapp_sat{t : Trail}{f : Formula}{a : ALit} :
  t.wf → a ∈ t → (t⊨ f  ↔ (t.remove a.name ++ [a]) ⊨ f) := by
  intro twf amem
  have remwf: (t.remove a.name ++ [a]).wf := Trail.wf_remapp twf amem
  simp[Satisfies.sat]
  constructor
  case mp =>
    intro call c cmem
    obtain ⟨ l, lc, lt ⟩ := call c cmem
    exists l
    simp[lc]
    obtain ⟨ b, bmem, bheq ⟩ := Trail.mem_lits_exists_mem lt
    cases Trail.remove_eq twf bmem amem
    case inl lh =>
      have := Trail.mem_mem_lits lh
      rw[Trail.lits_append]
      simp[←bheq, this]
    case inr rh =>
      simp[←bheq, rh, Trail.lits]
  case mpr =>
    intro call c cmem
    obtain ⟨ l, lc, lt ⟩ := call c cmem
    exists l
    simp[lc]
    obtain ⟨ b, bmem, bheq ⟩ := Trail.mem_lits_exists_mem lt
    simp[Trail.remove] at bmem
    cases bmem
    case inl lh =>
      have := Trail.mem_mem_lits lh.1
      simp[←bheq, this]
    case inr rh =>
      have := Trail.mem_mem_lits amem
      simp[←bheq, rh, this]


theorem appsat_remapp_sat{hd tl : Trail}{f : Formula}{a : ALit} :
  (hd++tl).wf → a ∈ hd → (hd++tl⊨ f ↔ (hd.remove a.name ++ [a]++tl) ⊨ f) := by
  intro twf amem
  constructor
  case mp =>
    intro h
    simp[Satisfies.sat] at h ⊢
    intro c cmem
    obtain ⟨ l, lc, lt ⟩ := h c cmem
    exists l
    simp[lc, Trail.lits] at lt ⊢
    cases lt
    case inl lh =>
      obtain ⟨ b, bmem, bheq ⟩ := lh
      by_cases heq : a = b
      case pos => simp[heq, bheq]
      case neg =>
        left
        exists b
        have := Trail.uniques (Trail.wf_append twf).1 heq amem bmem
        simp[Trail.remove, bmem, bheq]
        intro contra
        simp[contra] at this
    case inr rh => right; right; exact rh
  case mpr =>
    intro h
    simp[Satisfies.sat] at h ⊢
    intro c cmem
    obtain ⟨ l, lc, lt ⟩ := h c cmem
    exists l
    simp[lc, Trail.lits] at lt ⊢
    cases lt
    case inl lh =>
      obtain ⟨ b, bmem, bheq ⟩ := lh
      have := Trail.mem_remove_mem  bmem
      left
      exists b
    case inr rh =>
      cases rh
      case inl lh =>
        left
        exists a
        simp[amem, lh]
      case inr rh =>
        simp[rh]
