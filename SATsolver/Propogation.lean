import SATsolver.Assignments

theorem Clause.unit_elim (c : Clause)(t : Trail) :
    ∀ l : Lit, c.unitBy t ∧ t.undecided l ∧ l ∈ c.lits
    → ∀ t', t ⊆ t' → c.satisfiedBy t' = t'.satisfies l := by
    intro l lh t' t'SS
    simp[Clause.unitBy] at lh
    have ⟨ c_unit_t, l_undecided_t, l_mem_c ⟩ := lh
    rcases c_unit_t with ⟨ j, j_mem_c, j_undecided_t, non_j_fals ⟩
    by_cases l_eq_j : l = j
    case neg =>
        have := non_j_fals l l_mem_c l_eq_j
        have t_decided_l : t.decided l := by
            rw[←Trail.decided_iff_sat_or_falsifed]
            right; exact this
        contradiction
    subst l_eq_j
    apply iff_iff_eq.mp
    constructor
    case pos.mp =>
        intro c_sat_t'
        simp[Clause.satisfiedBy] at c_sat_t'
        rcases c_sat_t' with ⟨ j, ⟨ j_mem, t'sat_j ⟩ ⟩
        by_cases l_eq_j : j = l
        case neg =>
            have := non_j_fals j j_mem l_eq_j
            have := Trail.falsifies_subset_falsifies t'SS this
            have := Trail.satisfies_ne_falsifies t'sat_j
            contradiction
        subst l_eq_j
        exact t'sat_j
    case pos.mpr =>
        intro t'sat_l
        simp[satisfiedBy]
        exists l

def Clause.getUnit (c : Clause)(t : Trail)(wf : c.unitBy t) : Lit :=
    let l := c.lits.find? (fun l => t.undecidedB l)
    have is_some : l.isSome := by
        simp[←Clause.unit_iff_unitBy, Clause.unitByB] at wf
        split at wf
        case h_1 => contradiction
        case h_2 _ _ h => simp[l, h]
    l.get is_some

theorem Clause.getUnit_unseen {c : Clause}{t : Trail}(l : Lit)
    (wf : c.unitBy t) :
    l = c.getUnit t wf → t.undecided l := by
    intro h
    simp[←Clause.unit_iff_unitBy, Clause.unitByB, getUnit] at wf h
    split at wf
    case h_1 => contradiction
    case h_2 _ k h_k =>
        simp[h_k] at h
        have := List.find?_some h_k
        simp at this
        subst h
        exact this
