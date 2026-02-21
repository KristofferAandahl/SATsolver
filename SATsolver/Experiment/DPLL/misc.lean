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



theorem sublist_without_mem {e : α}{l : List α} :
  l.Nodup → e ∈ l → ∃ (l' : List α ), e ∉ l' ∧ ∀ (i : α), i ∈ l → i ≠ e → i ∈ l' := by
  intro nd emem
  induction l
  case nil => simp at emem
  case cons x xs ih =>
    cases emem
    case head =>
      exists xs
      constructor
      case left => simp [List.nodup_cons] at nd; exact nd.1
      case right =>
        intro i imem neq
        simpa[neq] using imem
    case tail emem =>
      simp [List.nodup_cons] at nd
      obtain ⟨ l', hall ⟩ := ih nd.2 emem
      exists (x::l')
      constructor
      case left =>
        simp[hall]
        intro contra
        rw[contra] at emem
        have := nd.1
        contradiction
      case right =>
        intro i imem neq
        cases imem
        case head => simp
        case tail imem =>
          have := hall.2 i imem neq
          simp[this]

def isEven (n : Nat) : Prop :=
  ∃ k, k * 2 = n

theorem doubleIseven{n : Nat} : isEven (n*2) := by simp[isEven]

def someFunction (n : Nat)(_ : isEven n) := 4

def callingSomeFunction (n : Nat) :=
  have doubleEven : isEven (n * 2) := by exact doubleIseven
  someFunction (n * 2) doubleEven

def returnFithElementOrThree (l : List Nat) :=
  if longer_than_five : l.length > 5 then l[5]'longer_than_five
  else 3


def subtract (n m : Nat)(_ : n > m) : Nat :=
  n - m

def sum : List Nat → Nat
  | [] => 0
  | n :: ns => n + sum ns
termination_by x => List.length x
