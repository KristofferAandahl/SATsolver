import SATsolver.data.Annotated

def Trail.invariant (t : List AnnotatedLit): Prop :=
  match t with
    | [] => true
    | x::xs => x ∉ xs ∧ x.getName ∉ xs.map (fun lit => lit.getName) ∧ invariant xs

structure Trail where
  trail : List AnnotatedLit
  inv : Trail.invariant trail

namespace Trail

instance : Membership AnnotatedLit Trail where
  mem t a := a ∈ t.trail

def empty : Trail :=
  ⟨ [], by simp[invariant] ⟩

def lits (t : Trail) : List Lit :=
  t.trail.map (fun a => a.getLiteral)

theorem mem_mem_lits (t : Trail)(a : AnnotatedLit):
  a ∈ t.trail → a.getLiteral ∈ t.lits := by
  simp[lits]
  induction t.trail with
  | nil => simp
  | cons x xs ih =>
    simp; intro h; cases h
    case inl h => left; simp[h]
    case inr h => right; exact ih h

theorem not_lits_not_mem(t : Trail)(a : AnnotatedLit):
  a.getLiteral ∉ t.lits → a ∉ t.trail := by
  simp[lits]
  induction t.trail with
  | nil => simp
  | cons x xs ih =>
    simp; intro ineq lit_ineq
    constructor
    intro contra; apply ineq; simp[contra]
    exact ih lit_ineq

theorem lits_exi_mem(t : Trail)(l : Lit):
  l ∈ t.lits → ∃ a ∈ t.trail, a.getLiteral = l := by
  cases t
  case mk t inv =>
    induction t with
    | nil => simp[lits]
    | cons x xs ih =>
      simp[lits]; intro h; cases h
      case inl leftH => left; simp[leftH]
      case inr rightH => right; exact rightH

def names (t : Trail) : List Nat :=
  t.trail.map (fun a => a.getName)

theorem mem_mem_names (t : Trail)(a : AnnotatedLit):
  a ∈ t.trail → a.getName ∈ t.names := by
  simp[names]
  induction t.trail with
  | nil => simp
  | cons x xs ih =>
    simp; intro h; cases h
    case inl h => left; simp[h]
    case inr h => right; exact ih h

theorem not_names_not_mem(t : Trail)(a : AnnotatedLit):
  a.getName ∉ t.names → a ∉ t.trail := by
  simp[names]
  induction t.trail with
  | nil => simp
  | cons x xs ih =>
    simp; intro ineq name_ineq
    constructor
    intro contra; apply ineq; simp[contra]
    exact ih name_ineq

theorem names_exi_mem(t : Trail)(n : Nat):
  n ∈ t.names → ∃ a ∈ t.trail, a.getName = n := by
  cases t
  case mk t inv =>
    induction t with
    | nil => simp[names]
    | cons x xs ih =>
      simp[names]; intro h; cases h
      case inl leftH => left; simp[leftH]
      case inr rightH => right; exact rightH

theorem mem_same_name (t : Trail)(a b : AnnotatedLit) :
  a ∈ t.trail → b ∈ t.trail → a.getName = b.getName → a = b := by
  intro a_mem b_mem name_eq
  rcases t with ⟨ trail, inv ⟩
  induction trail with
  | nil => simp at *
  | cons x xs ih =>
    simp at *
    cases a_mem; cases b_mem
    case inl.inl ha hb =>
      rw[ha, hb]
    case inl.inr ha hb =>
      subst ha
      have := inv.2.1
      simp at this
      have := this b hb
      symm at name_eq
      contradiction
    cases b_mem
    case inr.inl ha hb =>
      subst hb
      have := inv.2.1
      simp at this
      have := this a ha
      contradiction
    case inr.inr ha hb =>
      exact ih inv.2.2 ha hb


def get? (t : Trail)(l : Lit) : Option AnnotatedLit :=
  t.trail.find? (fun a => a.getName = l.getName)


@[simp]
theorem get?_some_iff_mem_names (t : Trail)(l : Lit) :
  (t.get? l).isSome = true ↔ l.getName ∈ t.names := by
  simp[get?]
  constructor
  intro h; cases h;
  case intro a ah =>
    rw[←ah.right]
    exact mem_mem_names t a ah.left
  intro h
  exact names_exi_mem t l.getName h

theorem get?_mems_lit (t : Trail)(a : AnnotatedLit):
  a ∈ t.trail → t.get? a.getLiteral = some a := by
  cases t
  case mk trail inv =>
  simp[get?]
  induction trail with
  | nil => simp
  | cons x xs ih =>
    intro h; simp at h ⊢;
    have name_inv : ∀ (x_1 : AnnotatedLit), x_1 ∈ xs → ¬x_1.getName = x.getName := by
      simp[invariant] at inv
      exact inv.right.left
    cases h
    case inl leftH => left; simp[leftH]
    case inr rightH =>
      right
      constructor
      case left =>
        have := name_inv a rightH
        intro contra; apply this; simp[contra]
      case right =>
        have := inv.2.2
        exact ih this rightH

theorem get?_lits_some_val (t : Trail)(l : Lit) :
  l ∈ t.lits → ∃ a, t.get? l = some a := by
  intro h
  obtain ⟨ a, ah ⟩ := lits_exi_mem t l h
  exists a
  rw[←ah.right]
  apply get?_mems_lit
  exact ah.left

theorem get?_names_some_val (t : Trail)(n : Nat) :
  n ∈ t.names → ∃ a l, l.getName = n → t.get? l = some a := by
  intro h
  obtain ⟨ a, ah ⟩ := t.names_exi_mem n h
  have := t.mem_mem_lits a ah.left
  exists a
  exists a.getLiteral
  simp[ah.right]
  exact t.get?_mems_lit a ah.left


theorem get?_eq_some_mem {l} (t : Trail)(a : AnnotatedLit):
  t.get? l = some a → a ∈ t.trail := by
  cases t
  case mk trail inv =>
  simp[get?]
  induction trail with
  | nil => simp
  | cons x xs ih =>
    intro h
    simp at h
    cases h
    case inl leftH => simp[←leftH.right]
    case inr rightH => simp[ih inv.right.right rightH.right]

@[simp]
theorem get?_eq_some_iff_mem (t : Trail)(a : AnnotatedLit):
  t.get? a.getLiteral = some a ↔ a ∈ t.trail := by
  constructor
  exact get?_eq_some_mem t a
  exact get?_mems_lit t a

@[simp]
theorem get?_eq_get?_neg (t : Trail)(l : Lit):
  t.get? (-l) = t.get? l := by
  simp[get?, Neg.neg]

def push (t : Trail)(a : AnnotatedLit)(wf : a.getName ∉ t.names) : Trail :=
  let t' := a::t.trail
  let inv' : invariant t' := by
    unfold invariant
    constructor
    case left => exact not_names_not_mem t a wf
    constructor
    case right.left =>
      simp; intro b b_mem;
      have b_name_mem := mem_mem_names t b b_mem
      intro contra
      rw[contra] at b_name_mem
      contradiction
    case right.right => exact t.inv
  ⟨ t', inv'⟩

theorem mem_push {t : Trail}{a b: AnnotatedLit}{wf : b.getName ∉ t.names} :
  a ∈ (t.push b wf).trail ↔ a = b ∨ a ∈ t.trail  := by
  simp[push]

theorem mem_names_push {t : Trail}{a : AnnotatedLit}{n : Nat}{wf : a.getName ∉ t.names} :
  n ∈ (t.push a wf).names ↔ n = a.getName ∨ n ∈ t.names := by
  simp[push, names]


def pop (t : Trail) : Trail :=
  have inv : Trail.invariant t.trail.tail := by
    rcases t with ⟨ trail, inv ⟩
    simp[List.tail]
    split
    case h_1 => simp[invariant]
    case h_2 _ x xs =>
      exact inv.2.2
  ⟨ t.trail.tail, inv ⟩

theorem pop_remove_head {t : Trail}{a : AnnotatedLit}{wf : t.trail ≠ []}:
  a = t.trail.head wf → a ∉ t.pop := by
  simp[pop]
  intro hhead
  rcases t with ⟨ trail, inv ⟩
  cases trail
  case nil => contradiction
  case cons b bs =>
    simp at *
    subst hhead
    exact inv.1

theorem pop_remove_head_name {t : Trail}{a : AnnotatedLit}{wf : t.trail ≠ []}:
  a = t.trail.head wf → a.getName ∉ t.pop.names := by
  simp[pop, names]
  intro hhead
  rcases t with ⟨ trail, inv ⟩
  cases trail
  case nil => contradiction
  case cons b bs =>
    have := inv.2.1
    simp at *
    subst hhead
    exact this

theorem inv_new_head_same_name {a b : AnnotatedLit}{as : List AnnotatedLit} :
  a.getName = b.getName → invariant (a::as) → invariant (b::as) := by
    unfold invariant
    intro hname a_inv
    have bname : ¬b.getName ∈ List.map (fun lit => lit.getName) as := by
      rw[hname] at a_inv
      exact a_inv.2.1
    constructor
    case left =>
      intro contra
      apply bname
      exact List.mem_map_of_mem contra
    case right =>
      constructor
      exact bname
      exact a_inv.2.2

theorem replace_no_dup {α}[BEq α] {a b c: α}{as : List α} :
  a ∉ as → a ≠ c → a ∉ as.replace b c := by
  intro hmem heq contra
  induction as with
  | nil => simp at contra
  | cons x xs ih =>
    simp[List.replace_cons] at contra
    by_cases hbeq : b==x
    case pos =>
      simp[hbeq] at contra hmem
      have hamem := hmem.right
      cases contra
      all_goals contradiction
    case neg =>
      simp[hbeq] at contra hmem
      have ⟨ haeq, hamem ⟩ :=  hmem
      rcases contra with _ | hmem_replace
      contradiction
      exact ih hamem hmem_replace

theorem replace_mem {α}[BEq α]{a b c: α}{as : List α} :
  a ∈ as.replace b c → a ∈ as ∨ a = c := by
  intro h
  induction as with
  | nil => simp at h
  | cons x xs ih =>
    simp[List.replace_cons] at h
    by_cases heq : b == x
    case pos =>
      simp [heq] at h
      rcases h with heq | hmem
      case inl => simp[heq]
      case inr => simp[hmem]
    case neg =>
      simp[heq] at h
      rcases h with heq | hmem
      case inl => simp[heq]
      case inr =>
        simp[hmem] at ih
        rcases ih with hmem | heq
        case inl => simp [hmem]
        case inr => simp[heq]


theorem inv_replace {a b : AnnotatedLit}{as : List AnnotatedLit} :
  invariant as → a.getName = b.getName → invariant (as.replace a b) := by
  intro inv hname
  induction as with
  | nil => simp[inv]
  | cons x xs ih =>
    by_cases hmem : a ∈ x::xs
    case neg =>
      rw[List.replace_of_not_mem hmem]
      exact inv
    case pos =>
      rw[List.replace_cons]
      by_cases heq₂ : a == x
      case pos =>
        simp at heq₂
        simp [heq₂]
        rw[←heq₂] at inv
        exact inv_new_head_same_name hname inv
      case neg =>
        simp[heq₂, inv.2.2] at ⊢ ih
        simp at heq₂
        simp[heq₂] at hmem
        have hname₂ : a.getName ≠ x.getName := by
          have := inv.2.1
          simp at this
          exact this a hmem
        rw[hname] at hname₂
        have heq₃ : b ≠ x := AnnotatedLit.name_ineq hname₂
        symm at heq₃
        unfold invariant
        constructor
        case left =>
          have := inv.1
          exact replace_no_dup this heq₃
        case right =>
          constructor
          case left =>
            simp
            intro y hmem₂
            have := replace_mem hmem₂
            rcases this with hmem₃ | heq₄
            case inl =>
              have := inv.2.1
              simp at this
              exact this y hmem₃
            case inr =>
              subst heq₄
              exact hname₂
          case right =>
            exact ih

def negate (t : Trail)(a : AnnotatedLit)(wf : a ∈ t.trail) : Trail :=
  let negated := a.negate
  let trail' := t.trail.replace a negated
  have inv' : invariant trail' := by
    have hname : a.getName = a.negate.getName := AnnotatedLit.name_negated
    rcases t with ⟨ trail, inv ⟩
    simp[trail']
    exact inv_replace inv hname
    ⟨ trail', inv' ⟩

theorem map_replace_eq_self_of_eq{l : List AnnotatedLit}{a b : AnnotatedLit}{f : AnnotatedLit → Nat}:
  f a = f b → (l.replace a b).map f = l.map f := by
  intro hfeq
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp[List.replace_cons]
    split
    case h_1 _ heq =>
      simp at heq
      simp[List.map]
      rw[←hfeq, ←heq]
    case h_2 _ heq =>
      simp[ih]


@[simp]
theorem names_negate {t : Trail}{a : AnnotatedLit}{mem : a ∈ t.trail} :
  (t.negate a mem).names = t.names := by
  simp[negate]
  have hname : a.getName = a.negate.getName := AnnotatedLit.name_negated
  rcases t with ⟨ trail, inv ⟩
  have : (trail.replace a a.negate).map AnnotatedLit.getName = trail.map AnnotatedLit.getName := map_replace_eq_self_of_eq hname
  simp[names, this]


instance : HasSubset Trail where
  Subset sub super := ∀ x ∈ sub.trail, x ∈ super.trail

theorem subset_empty (t : Trail):
  t ⊆ empty ↔ t = empty := by
  simp[HasSubset.Subset, empty]
  rcases t with ⟨ trail, inv ⟩
  constructor
  case mp =>
    intro h
    simp[List.eq_nil_iff_forall_not_mem, h]
  case mpr =>
    intro h
    simp at *
    simp[h]

theorem subset_self (t : Trail):
  t ⊆ t := by
  simp[HasSubset.Subset]

theorem subset_push_self(t : Trail):
  ∀ a (wf : a.getName ∉ t.names), t ⊆ t.push a wf := by
  simp[push]
  intro a a_new x x_mem
  simp[x_mem]

theorem mem_mem_subset(t : Trail)(a : AnnotatedLit):
  ∀ t', t' ⊆ t → a ∈ t' → a ∈ t := by
  simp[HasSubset.Subset]
  intro t' t'ss a_mem_t'
  exact t'ss a a_mem_t'

theorem lits_lits_subset{t t': Trail}{l : Lit}:
  t' ⊆ t → l ∈ t'.lits → l ∈ t.lits := by
  simp[lits]
  intro t'ss a a_mem_t' h_al
  exists a
  constructor
  exact mem_mem_subset t a t' t'ss a_mem_t'
  exact h_al

theorem names_names_subset {t t': Trail}{n : Nat}:
  t' ⊆ t → n ∈ t'.names → n ∈ t.names := by
  simp[names]
  intro t'ss a a_mem_t' h_an
  exists a
  constructor
  exact mem_mem_subset t a t' t'ss a_mem_t'
  exact h_an

theorem pop_subset {t : Trail}:
  t.pop ⊆ t := by
  simp[pop, HasSubset.Subset, List.tail]
  intro x hmem
  split at hmem
  case h_1 => contradiction
  case h_2 _ a as heq =>
    simp[heq, hmem]
