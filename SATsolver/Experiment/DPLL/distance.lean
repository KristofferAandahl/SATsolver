import SATsolver.Experiment.Relations.Theories
import SATsolver.Experiment.DPLL.misc
import SATsolver.Experiment.DPLL.decide
import SATsolver.Experiment.DPLL.propogate
import SATsolver.Experiment.DPLL.backtrack

/- Distance is a measure used to prove termination. The idea is that the first
differing element in a reversed trail decides the distance. For example a trail
with a deduced last element has always a smaller distance than a trail without-/

def distance_internal (soFar : Nat) : Trail → Nat → Nat
  | _, 0 => soFar
  | [], n+1 => distance_internal (soFar + 2*3^n) [] n
  | (ALit.decided _)::as, n+1 => distance_internal (soFar + 1*3^n) as n
  | (ALit.deduced _)::as, n+1 =>  distance_internal soFar as n

def distance_partial (soFar stop : Nat) : Trail → Nat → Nat
  | t, n =>
    if n ≤ stop then soFar
    else match t, n with
      | _, 0 => soFar
      | [], n+1 => distance_partial (soFar + 2 * 3 ^ n) stop [] n
      | (ALit.decided _) :: as, n+1 => distance_partial (soFar + 1 * 3 ^ n) stop as n
      | (ALit.deduced _) :: as, n+1 => distance_partial soFar stop as n

def distance(t : Trail)(v : Variables)(_ : v ≠ 0) : Nat :=
  distance_internal 0 t.reverse v

theorem extract_soFar {soFar n: Nat}{t : Trail}(x : Nat):
  distance_internal (soFar + x ) t n = soFar + distance_internal x t n := by
  induction n generalizing soFar x t with
  | zero => simp[distance_internal]
  | succ n ih =>
    cases t
    case nil => simp [distance_internal, Nat.add_assoc, ih]
    case cons a as =>
      cases a
      case decided a => simp [distance_internal, Nat.add_assoc, ih]
      case deduced a => simp [distance_internal, ih]

theorem extract_x {soFar n: Nat}{t : Trail}(x : Nat):
  distance_internal (soFar + x ) t n = x + distance_internal soFar t n := by
  induction n generalizing soFar x t with
  | zero => simp[distance_internal, Nat.add_comm]
  | succ n ih =>
    cases t
    case nil => simp [distance_internal, Nat.add_assoc, ih]
    case cons a as =>
      cases a
      case decided a => simp [distance_internal, Nat.add_assoc, ih]
      case deduced a => simp [distance_internal, ih]

theorem extract_from_partial {t} {soFar n s}(x) :
  distance_partial (soFar + x ) s t n = soFar + distance_partial x s t n := by
  induction n generalizing soFar t x s
  case zero => simp[distance_partial]
  case succ n ih =>
    cases t
    case nil =>
      simp[distance_partial]
      split
      case isTrue => rfl
      case isFalse => simp[Nat.add_assoc, ih]
    case cons a as =>
      cases a
      case decided a =>
        simp[distance_partial]
        split
        case isTrue => rfl
        case isFalse => simp[Nat.add_assoc, ih]
      case deduced a =>
        simp [distance_partial]
        split
        case isTrue => rfl
        case isFalse => simp[ih]

theorem distance_partial_zero {soFar n}{t} :
  distance_partial soFar 0 t n = distance_internal soFar t n := by
  induction n generalizing soFar t
  case zero => simp[distance_internal, distance_partial]
  case succ k ih =>
    cases t
    case nil => simp[distance_internal, distance_partial, ih]
    case cons a as =>
      cases a
      case decided l => simp[distance_internal, distance_partial, ih]
      case deduced l =>  simp[distance_internal, distance_partial, ih]

theorem distance_partial_n {soFar n}{t} :
  distance_partial soFar n t n = soFar := by
  unfold distance_partial
  simp

theorem split_internal {soFar n}{hd tl : Trail} :
  hd.length ≤ n → distance_internal soFar (hd++tl) n = distance_partial 0 (n-hd.length) hd n + distance_partial soFar 0 tl (n-hd.length) := by
  intro hlt
  induction hd generalizing n
  case nil => simp[distance_partial_n, distance_partial_zero]
  case cons x xs ih =>
    cases n
    case zero => simp at hlt
    case succ n =>
      cases x
      case decided =>
        simp[distance_internal, distance_partial]
        split
        case isTrue htrue =>
          have h1 : n - xs.length ≤ n := Nat.sub_le n xs.length
          have h2 : n < n + 1 := Nat.lt_succ_self n
          have := Nat.lt_of_le_of_lt h1 h2
          have := Nat.lt_le_asymm this
          contradiction
        case isFalse hfalse =>
          simp at hlt
          have : distance_partial (3 ^ n) (n - xs.length) xs n = (3 ^ n) + distance_partial 0 (n - xs.length) xs n := extract_from_partial 0
          simp[extract_x, this, ih hlt]
          simp +arith
      case deduced =>
        simp[distance_internal, distance_partial]
        split
        case isTrue htrue =>
          have h1 : n - xs.length ≤ n := Nat.sub_le n xs.length
          have h2 : n < n + 1 := Nat.lt_succ_self n
          have := Nat.lt_of_le_of_lt h1 h2
          have := Nat.lt_le_asymm this
          contradiction
        case isFalse hfalse =>
          simp at hlt
          simp[ih hlt]

theorem soFar_lt {x y n: Nat}{t : Trail}:
  x < y → distance_internal x t n < distance_internal y t n := by
  intro h
  have h1 : distance_internal x t n = x + distance_internal 0 t n := extract_soFar 0
  have h2 : distance_internal y t n = y + distance_internal 0 t n := extract_soFar 0
  rw[h1, h2]
  simp[h]

theorem distance_append {soFar n : Nat}{as: Trail}{a : ALit}:
  n > as.length → distance_internal soFar (as++[a]) n < distance_internal soFar as n := by
  induction as generalizing soFar n with
  | nil =>
    cases n with
    | zero => simp
    | succ n =>
      cases a
      case decided =>
        simp[distance_internal]
        have : soFar + 3 ^ n < soFar + 2 * 3 ^ n := by simp[arith_helper]
        simp[soFar_lt this]
      case deduced =>
        simp[distance_internal]
        have : soFar < soFar + 2 * 3 ^ n := by
            simp
            rw[←Nat.ne_zero_iff_zero_lt]
            simp[Nat.pow_eq_zero]
        simp[soFar_lt this]
  | cons b as ih =>
    intro h
    rw[List.length_cons] at h
    have : n ≠ 0 := by
      intro contra
      rw[contra] at h
      contradiction
    obtain ⟨ m, hm ⟩ := Nat.exists_eq_succ_of_ne_zero this
    have : m > as.length := by
      simp[hm] at h ⊢
      exact h
    cases b
    case decided => simp[hm, distance_internal, ih this]
    case deduced => simp[hm, distance_internal, ih this]

theorem helper {soFar n : Nat }{t : Trail} :
  distance_internal soFar t n < soFar + 3^n := by
  induction n generalizing t
  case zero => simp[distance_internal]
  case succ n ih =>
    cases t
    case nil =>
      simp[distance_internal, Nat.pow_succ]
      rw[Nat.add_comm]
      have : distance_internal (2 * 3 ^ n + soFar ) [] n = 2 * 3 ^ n + distance_internal (soFar) [] n := extract_soFar soFar
      rw[this]
      simp +arith
      exact ih
    case cons hd tl =>
      cases hd
      case deduced =>
        simp[distance_internal, Nat.pow_succ]
        have h₁ := ih (t := tl)
        apply Nat.lt_of_lt_of_le h₁
        simp +arith
      case decided =>
        simp[distance_internal, Nat.pow_succ]
        have : distance_internal (3 ^ n + soFar ) tl n = 3 ^ n + distance_internal (soFar) tl n := extract_soFar soFar
        rw[Nat.add_comm, this]
        simp +arith
        have h₁ := ih (t := tl)
        apply Nat.lt_of_lt_of_le h₁
        simp +arith

theorem head_subst{soFar n : Nat}{t y : Trail}{l j : Lit}:
  n ≠ 0 → distance_internal soFar ((ALit.deduced l)::y) n < distance_internal soFar ((ALit.decided j)::t) n := by
  intro nh
  obtain ⟨ k, kh ⟩ := Nat.exists_eq_succ_of_ne_zero nh
  simp[kh, distance_internal]
  have : distance_internal (soFar + 3 ^ k) t k = (soFar + 3 ^ k) + distance_internal 0 t k := extract_soFar 0
  rw[this]
  apply Nat.lt_add_right
  exact helper

theorem distance_dec {l : Lit}{t : Trail}{v: Variables}{lud : t ¿ l}{wf : v ≠ 0}:
  t.length < v → distance (dec l t lud) v wf < distance t v wf:= by
  intro h
  simp only [distance, dec, List.reverse_cons]
  apply distance_append
  simp[h]

theorem distance_prop{t : Trail}{c : Clause}{pwf : c.unit t}{v: Variables}{wf : v ≠ 0}:
  t.length < v → distance (propogate t c pwf) v wf < distance t v wf:= by
  intro h
  simp only [distance, propogate, List.reverse_cons]
  apply distance_append
  simp[h]

theorem distance_bc{t : Trail}{bcwf : ∃ a ∈ t, a.decidedP}{v: Variables}{wf : v ≠ 0}{twf : t.wf}:
  t.length ≤ v → distance (backtrack t bcwf twf) v wf < distance t v wf := by
  intro h
  obtain ⟨ hd, tl, a, heq, ha, hhd ⟩ := exists_split_on_prop ALit.decidedP t bcwf
  subst heq
  have : backtrack (hd ++ a :: tl) bcwf twf = ALit.deduced (a.lit.negate)::tl := backtrack_lemma hhd ha
  simp[this, distance]
  have hle : tl.reverse.length < v := by
    simp at h ⊢
    have : tl.length + 1 ≤ v := Nat.le_of_add_left_le h
    exact Nat.lt_of_succ_le this
  rw[split_internal, split_internal]
  simp[distance_partial_zero]
  cases a
  case deduced => simp[ALit.decidedP] at ha
  case decided l =>
    have : v - tl.length ≠ 0 := by
      have : tl.length < (hd ++ ALit.decided l :: tl).length := by simp +arith
      have := Nat.lt_of_lt_of_le this h
      apply Nat.ne_of_gt
      exact Nat.sub_pos_of_lt this
    simp only[ALit.lit]
    exact head_subst this
  exact Nat.le_of_lt hle
  exact Nat.le_of_lt hle
