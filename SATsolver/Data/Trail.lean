import SATsolver.Data.Annotated
namespace Trail

def uniqueness(stack : List AnnotatedLit) : Prop :=
  ∀ a ∈ stack, ∀ b ∈ stack, a ≠ b → a.getName ≠ b.getName

def consistency (stack : List AnnotatedLit) (names : Std.HashSet Nat): Prop :=
  (∀ lit ∈ stack, lit.getName ∈ names) ∧ (∀ name ∈ names, ∃ lit ∈ stack, lit.getName = name)

structure Trail where
  stack : List AnnotatedLit
  names : Std.HashSet Nat
  wf : uniqueness stack ∧ consistency stack names

theorem nin_names_nin_stack (lit : AnnotatedLit)(trail : Trail) :
  lit.getName ∉ trail.names → lit ∉ trail.stack := by
    intro h contra
    apply h
    cases trail
    case mk stack names wf =>
      simp at *
      have con := wf.right
      simp[consistency] at con
      have conL := con.left
      exact conL lit contra

def empty : Trail :=
  have wf : uniqueness [] ∧ consistency [] ∅  := by
    simp[uniqueness, consistency]
  {stack := [], names := ∅, wf := wf}

def add (as : Trail)(a : AnnotatedLit)(new : a.getName ∉ as.names): Trail :=
  let stack' := a :: as.stack
  let names' := as.names.insert a.getName
  /-Proving invariant-/
  have wf' : uniqueness stack' ∧ consistency stack' names' := by
    have new2 := nin_names_nin_stack a as new
    cases as
    case mk stack names wf =>
      simp at *
      let ⟨ unique, conL, conR ⟩ := wf
      simp[uniqueness, consistency] at *
      constructor
      case left =>
        intro b bin c cin bnc contra
        rw[List.mem_cons] at bin cin
        cases bin
        case inl bh =>
          cases cin
          case inl ch =>
            apply bnc
            rw[bh, ch]
          case inr ch =>
            apply new
            simp at ch
            have cName := conL c ch
            rw[←bh, contra]
            exact cName
        case inr bh =>
          cases cin
          case inl ch =>
            apply new
            simp at bh
            have bName := conL b bh
            rw[←ch, ←contra]
            exact bName
          case inr ch =>
            simp at *
            apply unique b bh c ch
            exact bnc
            exact contra
      case right =>
        constructor
        case left =>
          intro b bin
          rw[List.mem_cons] at bin
          cases bin
          case inl h =>
            rw[Std.HashSet.mem_insert, h]
            left
            simp
          case inr h =>
            simp at h
            have bn := conL b h
            rw[Std.HashSet.mem_insert]
            right
            exact bn
        case right =>
          intro N Nin
          simp[names'] at Nin
          cases Nin
          case inl hl =>
            exists a
            constructor
            rw[List.mem_cons]
            left
            rfl
            exact hl
          case inr hr =>
            have h := conR N hr
            cases h
            case intro b bh =>
              exists b
              constructor
              case left =>
                rw[List.mem_cons]
                right
                exact bh.left
              case right =>
                rw[bh.right]
  ⟨ stack', names', wf' ⟩


end Trail
