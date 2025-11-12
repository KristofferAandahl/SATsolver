import SATsolver.Propogation

inductive Clause.state where
  | fals : state
  | sat : state
  | unit :  (c : Clause) → (t : Trail) → c.unitByB t → state
  | undecided : state

def Clause.getState (c : Clause)(t : Trail) : Clause.state :=
  if c.falsifiedByB t then Clause.state.fals
  else if c.satisfiedByB t then Clause.state.sat
  else if unit : c.unitByB t then Clause.state.unit c t unit
  else Clause.state.undecided

inductive Formula.state where
  | conflict : state
  | sat : state
  | undecided : List Clause → state

def Formula.getState (f : Formula)(t : Trail) : Formula.state :=
  let cs : List Clause.state := f.map (fun c => c.getState t)
  if cs.any (fun s => match s with
                      | .fals => true
                      | _  => false ) then Formula.state.conflict
  else if cs.all (fun s => match s with
                      | .sat => true
                      | _  => false ) then Formula.state.sat
  else
    let units : List Clause := cs.filterMap (fun s => match s with
                                                | .unit c  _ _ => some c
                                                | _ => none )
    Formula.state.undecided units

def Formula.state.isUndecided (fs : Formula.state) : Prop :=
  match fs with
  | undecided _ => True
  | _ => False

theorem state_undecided_undecided {f : Formula}{t : Trail} :
  (f.getState t).isUndecided → f.undecidedBy t := by
  simp[Formula.state.isUndecided]
  intro h
  split at h
  case h_2 => contradiction
  case h_1 fs units hund =>
    simp[Formula.getState] at hund
    split at hund
    case isTrue  => contradiction
    split at hund
    case isTrue hsat => contradiction
    case isFalse hcon hsat =>
      simp at *
      simp[Formula.undecidedBy]
      constructor
      case left =>
        obtain ⟨ c, cmem, hsat ⟩ := hsat
        have not_sat : ¬c.satisfiedBy t := by
          split at hsat
          contradiction
          case h_2 s hsat' =>
            intro contra
            simp[Clause.getState, contra] at hsat'
            have := Clause.sat_neq_fals contra
            contradiction
        have not_fals : ¬c.falsifiedBy t := by
          have := hcon c cmem
          split at this
          contradiction
          case h_2 s hcon =>
            intro contra
            simp[Clause.getState, contra] at hcon
        exists c
        constructor
        case left => exact cmem
        case right =>
          apply Clause.undecided_if_not_decided
          simp[Clause.decidedBy]
          constructor
          exact not_fals
          exact not_sat
      case right =>
        intro c cmem
        have not_fals : ¬c.falsifiedBy t := by
          have := hcon c cmem
          split at this
          contradiction
          case h_2 s hcon =>
            intro contra
            simp[Clause.getState, contra] at hcon
        simp[Clause.fals_iff_not_sat_or_u] at not_fals
        by_cases cu : c.undecidedBy t
        case pos => left; exact cu
        case neg => right; exact not_fals cu

def Formula.state.units (fs : Formula.state)(wf : fs.isUndecided) : List Clause :=
  match fs with
  | undecided cs => cs


theorem Formula.getState.units_is_units {f: Formula}{t : Trail} :
    (h : (f.getState t).isUndecided) → ∀ c ∈ (f.getState t).units h, c.unitBy t := by
    simp[state.isUndecided]
    intro h c hmem
    split at h
    case h_2 => contradiction
    case h_1 h' fs lc heq =>
      simp [heq] at hmem
      simp [state.units] at hmem
      simp[getState] at heq
      split at heq
      case isTrue =>
        simp at heq -- Sate is conflict -> Contradiction
      case isFalse =>
        split at heq
        case isTrue =>
          simp at heq -- Sate is sat -> Contradiction
        case isFalse =>
          simp at heq
          rw[←heq] at hmem
          simp [List.mem_filterMap] at hmem
          rcases hmem with ⟨ x, ⟨ xmem, h ⟩ ⟩
          split at h
          case h_2 => contradiction
          case h_1 s y t' hunit heq =>
            simp at h
            rw[h] at hunit
            simp[Clause.getState] at heq
            split at heq
            contradiction
            split at heq
            contradiction
            split at heq
            simp at heq
            simp[←Clause.unit_iff_unitBy, heq, hunit]
            contradiction



def SolverState.invariant (ns : List Nat)(t : Trail)(f : Formula) : Prop :=
  ns.Nodup ∧ (∀ n ∈ ns, n ∉ t.names) ∧ f ≠ [] ∧ f.wf ∧ (∀ n ∈ f.names, n ∈ t.names ∨ n ∈ ns)

structure SolverState where
  ns : List Nat
  t : Trail
  f : Formula
  inv : SolverState.invariant ns t f


theorem SolverState.learn_lit {s : SolverState}{a : AnnotatedLit}{wf : s.ns ≠ []} :
  a.getName = s.ns.head wf → (unseen : a.getName ∉ s.t.names) → SolverState.invariant s.ns.tail (s.t.push a unseen) s.f := by
  intro head unseen
  simp[SolverState.invariant]
  rcases s with ⟨ ns , t , f, inv ⟩
  constructor
  case left =>
    cases ns
    case nil => simp
    case cons x xs => simp [List.nodup_cons.mp inv.1]
  case right =>
    constructor
    case left =>
      intro m hmem
      simp[Trail.mem_names_push] at hmem ⊢
      constructor
      case left =>
        cases ns
        case nil => simp at hmem
        case cons x xs =>
          simp at head hmem
          rw[head]
          intro contra
          apply (List.nodup_cons.mp inv.1).left
          simp[←contra, hmem]
      case right =>
        have hmem := List.mem_of_mem_tail hmem
        exact inv.right.left m hmem
    case right =>
      constructor
      case left =>
        simp
        exact inv.2.2.1
      constructor
      case left =>
        simp
        exact  inv.2.2.2.1
      case right =>
        intro m hle
        have := inv.2.2.2.2
        simp at *
        have := this m hle
        simp[Trail.mem_names_push]
        cases this
        case inl h =>
          left; right; exact h
        case inr h =>
          simp[head]
          cases ns
          case nil => contradiction
          case cons x xs =>
            simp at h ⊢
            rcases h with h | h
            left; left; exact h
            right; exact h



namespace DPLL

def decide (s : SolverState)(k : Nat)(wf : s.ns ≠ []) : SolverState :=
  let l := Lit.pos (s.ns.head wf)
  let a := AnnotatedLit.decided l (k + 1)
  have unseen : a.getName ∉ s.t.names := by
    have ln_mem : l.getName ∈ s.ns := by simp[l, Lit.getName]
    have unseen : l.getName ∉ s.t.names := s.inv.2.1 l.getName ln_mem
    have : a.getName = l.getName := by simp[a, AnnotatedLit.getName]
    simp[this, unseen]
  let t' := s.t.push a unseen
  let ns' := s.ns.tail
  have inv' : SolverState.invariant ns' t' s.f := by
    simp[ns', t']
    have : l.getName = a.getName := by simp[a, AnnotatedLit.getName]
    simp[l, Lit.getName] at this
    symm at this
    exact SolverState.learn_lit this unseen
  ⟨ ns', t', s.f, inv' ⟩

theorem decide_add_pos_decision {s : SolverState}{k : Nat}
  {wf : s.ns ≠ []}(unseen : s.ns.head wf ∉ s.t.names):
  (decide s k wf).t = s.t.push (AnnotatedLit.decided (Lit.pos (s.ns.head wf)) (k+1)) unseen := by
  simp[decide]

theorem decide_f_unchanged {s : SolverState}{k : Nat}{wf : s.ns ≠ []}:
  (decide s k wf).f = s.f := by
  simp[decide]

def forget(s : SolverState)(wf : s.t.trail ≠ []): SolverState :=
  let a := s.t.trail.head wf
  let n := a.getName
  let ns' := n :: s.ns
  let t' := s.t.pop
  have inv' : SolverState.invariant ns' t' s.f := by
    simp[SolverState.invariant, ns']
    constructor
    constructor
    case left.left =>
      have : n ∈ s.t.names := by
        have mem : a ∈ s.t.trail := by simp[a]
        have := Trail.mem_mem_names s.t a mem
        simp[AnnotatedLit.getName, Lit.getName] at this
        exact this
      intro contra
      apply s.inv.2.1 n contra
      exact this
    case left.right =>
      exact s.inv.1
    case right =>
      constructor
      constructor
      case left.left =>
        have : a = s.t.trail.head wf := by rfl
        have : a.getName ∉ t'.names := Trail.pop_remove_head_name this
        have hname : n = a.getName := by simp[n, AnnotatedLit.getName, Lit.getName]
        simp[hname, this]
      case left.right =>
        intro m hmem contra
        have hinv : ¬m ∈ s.t.names := s.inv.2.1 m hmem
        have : t' ⊆ s.t := Trail.pop_subset
        have : m ∈ s.t.names := Trail.names_names_subset this contra
        contradiction
      case right =>
        constructor
        case left =>
          exact s.inv.2.2.1
        constructor
        case left =>
          exact s.inv.2.2.2.1
        case right =>
          intro m hle
          have hinv := s.inv.2.2.2.2 m hle
          cases hinv
          case inl hmem =>
            have head : a = s.t.trail.head wf := by rfl
            have := (Trail.mem_pop_ne_head_names head).right m hmem
            simp[n, t']
            by_cases heq : m = a.getName
            right; left; exact heq
            left; exact this heq
          case inr hmem =>
            right; right; exact hmem
  ⟨ ns', t', s.f, inv' ⟩

theorem forget_reduces {s : SolverState}{wf : s.t.trail ≠ []} :
  (forget s wf).t.trail.length < s.t.trail.length := by
  simp[forget, Trail.pop]
  have l_neq_zero : s.t.trail.length ≠ 0 := by
    intro contra
    rw[List.length_eq_zero_iff] at contra
    contradiction
  exact Nat.sub_one_lt l_neq_zero

def backtrack (s : SolverState) (k : Nat) : SolverState × Nat :=
  if not_nil : ¬s.t.trail.isEmpty then
    have not_nil : s.t.trail ≠ [] := by
      simp at not_nil
      exact not_nil
    let a := s.t.trail.head not_nil
    have mem : a ∈ s.t.trail := by simp[a]
    match hcase : a with
    | AnnotatedLit.decided (Lit.pos n) m =>
      let t' := s.t.negate (AnnotatedLit.decided (Lit.pos n) m) mem
      have inv' : SolverState.invariant s.ns t' s.f := by
        simp[SolverState.invariant]
        simp[t', s.inv.1]
        exact s.inv.2
      (⟨ s.ns, t', s.f, inv' ⟩, m)
    | AnnotatedLit.decided _ m => backtrack (forget s not_nil) m
    | _ => backtrack (forget s not_nil) k
  else ⟨ s, 0 ⟩
termination_by s.t.trail.length
  decreasing_by
  exact forget_reduces
  exact forget_reduces

theorem List.nodup_erase_nodup {α}[BEq α][LawfulBEq α]{l : List α}{a : α} :
  l.Nodup → (l.erase a).Nodup := by
  intro h
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp[List.erase_cons]
    split
    case isTrue =>
      simp at h
      exact h.right
    case isFalse =>
      simp at *
      constructor
      case left hne =>
        intro contra
        apply h.left
        exact (List.mem_erase_of_ne hne).mp contra
      case right =>
        exact ih h.right

theorem List.nodup_erase_self_ne_mem {α}[BEq α][LawfulBEq α]{l : List α}(a : α) :
  l.Nodup → a ∉ (l.erase a) := by
  intro h
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp[List.erase_cons]
    split
    case isTrue heq =>
      simp at h heq
      simp[←heq, h]
    case isFalse hne =>
      simp at h hne ⊢
      constructor
      case left => intro contra; rw[contra] at hne; contradiction
      case right => exact ih h.right


def propogate (s : SolverState)(c : Clause)(wf : c.unitBy s.t) : SolverState :=
  let l := c.getUnit s.t wf
  have undecided : l.getName ∉ s.t.names:= by
      have : l = c.getUnit s.t wf := by
          simp[l]
      exact Clause.getUnit_unseen l wf this
  let a := AnnotatedLit.propogated l c
  have unseen : a.getName ∉ s.t.names := by
      rw[←AnnotatedLit.simp_getName]
      simp[AnnotatedLit.getLiteral, a]
      exact undecided
  let ns' := s.ns.erase l.getName
  let t' := s.t.push a unseen
  have inv' : SolverState.invariant ns' t' s.f := by
    simp[ns', t', SolverState.invariant]
    rcases s with ⟨ ns, t, N, inv ⟩
    constructor
    case left => exact List.nodup_erase_nodup inv.1
    case right =>
      simp
      constructor
      case left =>
        intro m hmem
        simp[Trail.mem_names_push] at ⊢
        constructor
        case left =>
          intro contra
          have hname : l.getName = a.getName := by simp[a, AnnotatedLit.getName]
          rw[hname, ←contra] at hmem
          apply List.nodup_erase_self_ne_mem m inv.1
          exact hmem
        case right =>
          have := List.mem_of_mem_erase hmem
          exact inv.2.1 m this
      case right =>
        constructor
        case left =>
          exact inv.2.2.1
        constructor
        exact inv.2.2.2.1
        case right =>
          intro m hle
          have hinv := inv.2.2.2.2 m hle
          cases hinv
          case inl hmem =>
            left; simp[Trail.mem_names_push]; right; exact hmem
          case inr hmem =>
            have : l.getName = a.getName := by simp [a, AnnotatedLit.getName]
            rw[this]
            by_cases heq : m = a.getName
            case pos =>
              left; simp [Trail.names, Trail.push]
              left; exact heq
            case neg =>
              right; simp[List.mem_erase_of_ne heq, hmem]
  ⟨ ns', t', s.f, inv' ⟩


abbrev Distance : Type := List Nat

def distanceHelper (soFar : Distance) : Nat → List AnnotatedLit → Distance
  | 0, _  => soFar
  | n+1, [] => distanceHelper (soFar++[2]) n []
  | n+1, a::as => if a.isPos
                  then distanceHelper (soFar++[1]) n as
                  else distanceHelper (soFar++[0]) n as

theorem append_sofar_append {x n : Nat}{d : Distance}{as : List AnnotatedLit} :
  x :: distanceHelper d n as = distanceHelper (x::d) n as := by
  induction n generalizing d as with
  | zero => simp[distanceHelper]
  | succ n ih =>
    cases as
    case nil =>
      simp[distanceHelper]
      apply ih
    case cons =>
      simp[distanceHelper]
      split
      case isTrue => apply ih
      case isFalse => apply ih

def Distance.distance (s : SolverState) : Distance :=
  (distanceHelper [] s.f.names.length (s.t.trail).reverse)

theorem mem_distance_helper_le2 {n : Nat}{soFar : Distance}{as : List AnnotatedLit}(wf : ∀ d ∈ soFar, d ≤ 2) :
  ∀ d ∈ distanceHelper soFar n as, d ≤ 2 := by
  intro d dh
  induction n generalizing soFar as with
  | zero =>
    simp[distanceHelper] at dh
    exact wf d dh
  | succ n ih =>
    have lemma: ∀ n ≤ 2, ∀ d ∈ soFar ++ [n], d ≤ 2 := by
      simp
      intro n nh d dh
      cases dh
      case inl hmem => exact wf d hmem
      case inr heq => simp[heq, nh]
    cases as with
    | nil =>
      simp[distanceHelper] at dh
      have : ∀ (d : Nat), d ∈ soFar ++ [2] → d ≤ 2 := lemma 2 (by simp)
      exact ih this dh
    | cons a as =>
      simp[distanceHelper] at dh
      split at dh
      case isTrue =>
        have : ∀ (d : Nat), d ∈ soFar ++ [1] → d ≤ 2 := lemma 1 (by simp)
        exact ih this dh
      case isFalse =>
        have : ∀ (d : Nat), d ∈ soFar ++ [0] → d ≤ 2 := lemma 0 (by simp)
        exact ih this dh


theorem mem_distance_le2 {s : SolverState} :
  ∀ d ∈ Distance.distance s, d ≤ 2 := by
  simp[Distance.distance]
  have : ∀ (n : Nat), n ∈ [] → n ≤ 2 := by simp
  exact mem_distance_helper_le2 this


def weightHelper (soFar : Nat) : (d : Distance) → (∀ n ∈ d, n ≤ 2) → Nat
  | [], _ => soFar
  | a :: as, h =>
    have h' : (∀ n ∈ as, n ≤ 2) := by
      intro n nh
      have : n ∈ a::as := List.mem_cons_of_mem a nh
      exact h n this
    weightHelper (soFar + (a * 3 ^ (a::as).length)) as h'

def Distance.weight (d : Distance)(wf : ∀ n ∈ d, n ≤ 2): Nat :=
  weightHelper 0 d wf

def Distance.lt : Distance → Distance → Prop
  | [], [] => False
  | _::_, [] => False
  | a::as, b::bs => if a < b then True
                    else if a = b then Distance.lt as bs
                    else False
  | [], _::_ => True

instance : LT Distance where
  lt as bs := Distance.lt as bs

theorem distance_lt_iff_weight_lt {as bs : Distance} (aswf : ∀ a ∈ as, a ≤ 2) (bswf : ∀ b ∈ bs, b ≤ 2):
  as < bs ↔ as.weight aswf < bs.weight bswf := by
  constructor
  case mp =>
    intro h
    induction as generalizing bs with
    | nil =>
      simp[Distance.weight]
      induction bs with
      | nil => simp[LT.lt, Distance.lt] at h
      | cons x xs ih =>





theorem distance_helper_len {x y : Nat}{d : Distance}{as : List AnnotatedLit} :
  d.length + x = y → (distanceHelper d x as).length = y := by
  induction x generalizing d as with
  | zero => simp[distanceHelper]
  | succ n ih =>
    cases as
    case nil =>
      simp[distanceHelper]
      intro h
      have : (d ++ [2]).length + n = y := by
        simp[List.length_append, Nat.add_assoc]
        rw[Nat.add_comm 1 n]
        exact h
      exact ih this
    case cons a as =>
      simp[distanceHelper]
      intro h
      split
      case isTrue =>
        have : (d ++ [1]).length + n = y := by
          simp[List.length_append, Nat.add_assoc]
          rw[Nat.add_comm 1 n]
          exact h
        exact ih this
      case isFalse =>
        have : (d ++ [0]).length + n = y := by
          simp[List.length_append, Nat.add_assoc]
          rw[Nat.add_comm 1 n]
          exact h
        exact ih this

theorem distance_len_eq_n {s : SolverState} :
  (Distance.distance s).length = s.f.names.length := by
  simp[Distance.distance]
  rcases s with ⟨ ns, t, f, inv⟩
  induction f.names.length generalizing t with
  | zero => simp[distanceHelper]
  | succ n ih =>
    simp at *
    have : ([] : List Nat).length + (n + 1) = n + 1 := by simp
    exact distance_helper_len this

theorem distance_range_trail {s : SolverState} :
  ∀ (b₁ : i < s.t.trail.length), (b₂ : i < (Distance.distance s).length) →
  ((s.t.trail[i]'b₁).isPos → (Distance.distance s)[i]'b₂ = 1) ∧
  (¬(s.t.trail[i]'b₁).isPos → (Distance.distance s)[i]'b₂ = 0) := by
  intro b₁ b₂
  simp[distance_len_eq_n] at b₂
  constructor
  case left =>
    simp[Distance.distance, ]

theorem distance_decide {s : SolverState}{k : Nat}{wf : s.ns ≠ []} :
  i = (decide s k wf).t.trail.length →
  (Distance.distance (decide s k wf))[i]? = some 1 ∧ (Distance.distance s)[i]? = some 2 ∧
  ∀ n ≠ i, (Distance.distance (decide s k wf))[i]? = (Distance.distance s)[i]?
  := by
  intro h



theorem state_undecided_some_undecided{s : SolverState} :
  (s.f.getState s.t).isUndecided → s.ns ≠ [] := by
  intro h
  have hu := state_undecided_undecided h
  have unseen := Formula.undecided_trail_incomplete hu s.inv.2.2.1
  have := s.inv.2.2
  obtain ⟨ n, nMemF, nNMemT ⟩ := unseen
  have : n ∈ s.t.names ∨ n ∈ s.ns := s.inv.2.2.2.2 n nMemF
  simp[nNMemT] at this
  intro contra
  rw[contra] at this
  contradiction

def internal(s : SolverState)(k : Nat): Formula.state :=
  let state := s.f.getState s.t
  match hs: state with
  | .conflict =>
    let ⟨ s', k'⟩ := backtrack s k
    if backtrack s k then state
    else internal (backtrack s k)
  | .sat => state
  | .undecided unit_cs =>
    have not_nil : s.ns ≠ [] := by
      simp [state] at hs
      have : (s.f.getState s.t).isUndecided := by
        simp[Formula.state.isUndecided, hs]
      exact state_undecided_some_undecided this
    if hempty : unit_cs.isEmpty then internal (decide s k not_nil) (k+1)
    else
      have not_nil : unit_cs ≠ [] := by
        simp at hempty
        exact hempty
      let c := unit_cs.head not_nil
      have unit_head_unit : c.unitBy s.t := by
        have state_und : state.isUndecided := by
          simp[Formula.state.isUndecided, hs]
        have : (s.f.getState s.t).units state_und = unit_cs := by
          simp[Formula.state.units]
          split
          case h_1 fs wf cs wf heq₁ heq=>
            simp [state, heq₁] at hs
            exact hs
        have all_units := Formula.getState.units_is_units state_und c
        have c_mem : c ∈ unit_cs := List.head_mem not_nil
        simp[this, c_mem] at all_units
        exact all_units
      internal (propogate s c unit_head_unit) k
termination_by (Distance.distance s).weight
  decreasing_by
