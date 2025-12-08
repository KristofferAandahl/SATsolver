theorem exists_split_on_prop{α : Type _} (p : α → Prop)(t : List α)(h : ∃ e ∈ t, p e) :
    ∃ hd tl a, t = hd ++ a :: tl ∧ p a ∧ ∀ x ∈ hd, ¬ p x := by
    induction t
    case nil => simp at h
    case cons x xs ih =>
      by_cases hx : p x
      case pos =>
        exists [], xs
        simp[hx]
      case neg =>
        have : (∃ e, e ∈ xs ∧ p e) := by
          obtain ⟨ e, hmem, he ⟩ := h
          cases hmem
          case head => contradiction
          case tail hmem => exists e
        obtain ⟨ hd, tl, a, h ⟩ := ih this
        exists (x::hd), tl, a
        simp[hx, h]
        intro b bmem
        exact h.2.2 b bmem

theorem arith_helper {n : Nat} :
  3 ^ n < 2 * 3 ^ n := by
  induction n
  case zero => simp
  case succ n ih =>
    simp[Nat.pow_succ, ←Nat.mul_assoc, ih]
