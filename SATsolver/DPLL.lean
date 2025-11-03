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



def SolverState.invariant (ns : List Nat)(t : Trail)(N : Nat) : Prop :=
  ns.Nodup ∧ (∀ n ∈ ns, n ∉ t.names) ∧ (∀ n ∈ List.range N, n ∈ t.names ∨ n ∈ ns)

structure SolverState where
  ns : List Nat
  t : Trail
  N : Nat
  inv : SolverState.invariant ns t N


theorem SolverState.learn_lit {s : SolverState}{a : AnnotatedLit}{wf : s.ns ≠ []} :
  a.getName = s.ns.head wf → (unseen : a.getName ∉ s.t.names) → SolverState.invariant s.ns.tail (s.t.push a unseen) s.N := by
  intro head unseen
  simp[SolverState.invariant]
  rcases s with ⟨ ns , t , N, inv ⟩
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
      intro m hless
      have := inv.2.2
      simp at *
      have := this m hless
      cases this
      simp[Trail.mem_names_push]
      case inl h =>
        simp h
      case inr h =>




namespace DPLL

def decide (s : SolverState)(l : Lit)(k : Nat)
  (wf : s.ns ≠ [])(head : l.getName = s.ns.head wf): SolverState × Nat :=
  let a := AnnotatedLit.decided l (k + 1)
  have unseen : a.getName ∉ s.t.names := by
    have ln_mem : l.getName ∈ s.ns := by simp[head]
    have unseen : l.getName ∉ s.t.names := s.inv.2 l.getName ln_mem
    have : a.getName = l.getName := by simp[a, AnnotatedLit.getName]
    simp[this, unseen]
  let t' := s.t.push a unseen
  let ns' := s.ns.tail
  have inv' : SolverState.invariant ns' t' := by
    simp[ns', t']
    have : l.getName = a.getName := by simp[a, AnnotatedLit.getName]
    rw[this] at head
    exact SolverState.learn_lit head unseen
  ( ⟨ ns', t', s.nLits, inv' ⟩, k+1 )

def forget(s : SolverState)(wf : s.t.trail ≠ []): SolverState :=
  let a := s.t.trail.head wf
  let n := a.getName
  let ns' := n :: s.ns
  let t' := s.t.pop
  have inv' : SolverState.invariant ns' t' := by
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
      apply s.inv.2 n contra
      exact this
    case left.right =>
      exact s.inv.1
    constructor
    case right.left =>
      have : a = s.t.trail.head wf := by rfl
      have : a.getName ∉ t'.names := Trail.pop_remove_head_name this
      have hname : n = a.getName := by simp[n, AnnotatedLit.getName, Lit.getName]
      simp[hname, this]
    case right.right =>
      intro m hmem contra
      have hinv : ¬m ∈ s.t.names := s.inv.2 m hmem
      have : t' ⊆ s.t := Trail.pop_subset
      have : m ∈ s.t.names := Trail.names_names_subset this contra
      contradiction
  ⟨ ns', t', s.nLits, inv' ⟩

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
      have inv' : SolverState.invariant s.ns t' := by
        simp[SolverState.invariant]
        simp[t', s.inv.1]
        exact s.inv.2
      (⟨ s.ns, t', s.nLits, inv' ⟩, m)
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
  have inv' : SolverState.invariant ns' t' := by
    simp[ns', t', SolverState.invariant]
    rcases s with ⟨ ns, t, _, inv ⟩
    constructor
    case left => exact List.nodup_erase_nodup inv.1
    case right =>
      simp
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
        exact inv.2 m this
  ⟨ ns', t', s.nLits, inv' ⟩

abbrev Distance : Type := List Nat

def distanceHelper (soFar : Distance) : Nat → List AnnotatedLit → Distance
  | 0, _  => soFar
  | n+1, [] => distanceHelper (2::soFar) n []
  | n+1, a::as => if a.isPos
                  then distanceHelper (1::soFar) n as
                  else distanceHelper (0::soFar) n as

def Distance.distance (s : SolverState) : Distance :=
  (distanceHelper [] s.nLits s.t.trail).reverse

def weightHelper (soFar : Nat) : Distance → Nat
  | [] => soFar
  | a :: as => weightHelper (soFar + (a * as.length)) as

def Distance.weight (d : Distance): Nat :=
  weightHelper 0 d

def Distance.lt : Distance → Distance → Prop
  | _::_, [] => True
  | a::as, b::bs => if a < b then True
                    else if a = b then Distance.lt as bs
                    else False
  | [], _ => False

instance : LT Distance where
  lt as bs := Distance.lt as bs


def internal(f : Formula)(s : SolverState)(k : Nat): Formula.state :=
  let state := f.getState s.t
  match hs: state with
  | .conflict =>
    let ⟨ s', k'⟩ := backtrack s k
    if k' = 0 then state
    else internal f s' k'
  | .sat => state
  | .undecided unit_cs =>
    have not_nil : s.ns ≠ [] := by
      sorry
    if hempty : unit_cs.isEmpty then internal f (decide s k not_nil) (k+1)
    else
      have not_nil : unit_cs ≠ [] := by
        simp at hempty
        exact hempty
      let c := unit_cs.head not_nil
      have unit_head_unit : c.unitBy s.t := by
        have state_und : state.isUndecided := by
          simp[Formula.state.isUndecided, hs]
        have : (f.getState s.t).units state_und = unit_cs := by
          simp[Formula.state.units]
          split
          case h_1 fs wf cs wf heq₁ heq=>
            simp [state, heq₁] at hs
            exact hs
        have all_units := Formula.getState.units_is_units state_und c
        have c_mem : c ∈ unit_cs := List.head_mem not_nil
        simp[this, c_mem] at all_units
        exact all_units
      internal f (propogate s c unit_head_unit) k
termination_by (Distance.distance s).weight
  decreasing_by


def dpll (f : Formula)
