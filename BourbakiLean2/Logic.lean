universe u v

@[simp] theorem Sigma.eta {α : Type u} {β : α → Type v} {x : Sigma β} : ⟨x.1, x.2⟩ = x := by
  rcases x
  rfl


variable {p q : Prop}
/-- Any implication is equivalent to its converse. -/
theorem imp_iff_not_imp_not : (p → q) ↔ (¬ q → ¬ p) := by
  constructor
  · exact fun h h' h'' => h' (h h'')
  · intro h h'
    by_cases h'' : q
    · exact h''
    · exact (h h'' h').elim

theorem func_subsingleton_iff_to_empty {α : Type u} {β : Type v} (h : α → Empty) : Subsingleton (α → β) := by
  constructor
  intro a b
  ext c
  rcases h c

/-- transporting a proof along a path with the same basepoints doesnt yield anything new -/
@[simp] theorem eq_rec_self {α : Sort u} {x : α → Sort u} {a} {h : a = a} {h' : x a} :
  @Eq.rec α a (fun x_1 _ ↦ x x_1) h' a h = h' := by
  rcases h
  rfl
/-- transporting a proof along a path with the same basepoints in reverse doesnt yield anything new -/
@[simp] theorem eq_rec_symm_self {α : Sort u} {x : α → Sort u} {a} {h : a = a} {h' : x a} :
  @Eq.rec α a (fun x_1 _ ↦ x x_1) h' a h.symm = h' := by
  rcases h
  rfl


attribute [simp] Subtype.eq_iff

@[ext]
structure Unique (α : Sort u) extends Inhabited α where
  /-- In a `Unique` type, every term is equal to the default element (from `Inhabited`). -/
  uniq : ∀ a : α, a = default

attribute [class] Unique

instance PUnit.unique : Unique PUnit.{u} where
  default := PUnit.unit
  uniq x := subsingleton x _

@[simp]
theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit :=
  rfl

/-- Every provable proposition is unique, as all proofs are equal. -/
def uniqueProp {p : Prop} (h : p) : Unique.{0} p where
  default := h
  uniq _ := rfl

/-- `True` has a unique term. -/
instance : Unique True :=
  uniqueProp trivial

namespace Unique

open Function

section

variable {α : Sort u} [Unique α]

-- see Note [lower instance priority]
instance (priority := 100) : Inhabited α :=
  toInhabited ‹Unique α›

theorem eq_default (a : α) : a = default :=
  uniq _ a

theorem default_eq (a : α) : default = a :=
  (uniq _ a).symm

-- see Note [lower instance priority]
instance (priority := 100) instSubsingleton : Subsingleton α where
  allEq _ _ := Eq.trans (eq_default _) (eq_default _).symm

theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ p default :=
  ⟨fun h ↦ h _, fun h x ↦ by rwa [Unique.eq_default x]⟩

theorem exists_iff {p : α → Prop} : Exists p ↔ p default :=
  ⟨fun ⟨a, ha⟩ ↦ eq_default a ▸ ha, Exists.intro default⟩

end


def ExistsUnique {α : Type u} (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x
open Lean


/--
Checks to see that `xs` has only one binder.
-/
def isExplicitBinderSingular (xs : TSyntax ``explicitBinders) : Bool :=
  match xs with
  | `(explicitBinders| $_:binderIdent $[: $_]?) => true
  | `(explicitBinders| ($_:binderIdent : $_)) => true
  | _ => false

open TSyntax.Compat in
/--
`∃! x : α, p x` means that there exists a unique `x` in `α` such that `p x`.
This is notation for `ExistsUnique (fun (x : α) ↦ p x)`.

This notation does not allow multiple binders like `∃! (x : α) (y : β), p x y`
as a shorthand for `∃! (x : α), ∃! (y : β), p x y` since it is liable to be misunderstood.
Often, the intended meaning is instead `∃! q : α × β, p q.1 q.2`.
-/
macro "∃!" xs:explicitBinders ", " b:term : term => do
  if !isExplicitBinderSingular xs then
    Macro.throwErrorAt xs "\
      The `ExistsUnique` notation should not be used with more than one binder.\n\
      \n\
      The reason for this is that `∃! (x : α), ∃! (y : β), p x y` has a completely different \
      meaning from `∃! q : α × β, p q.1 q.2`. \
      To prevent confusion, this notation requires that you be explicit \
      and use one with the correct interpretation."
  expandExplicitBinders ``ExistsUnique xs b

@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! $x:ident : $t, $b)
  | _                                               => throw ()

/--
`∃! x ∈ s, p x` means `∃! x, x ∈ s ∧ p x`, which is to say that there exists a unique `x ∈ s`
such that `p x`.
Similarly, notations such as `∃! x ≤ n, p n` are supported,
using any relation defined using the `binder_predicate` command.
-/
syntax "∃! " binderIdent binderPred ", " term : term

macro_rules
  | `(∃! $x:ident $p:binderPred, $b) => `(∃! $x:ident, satisfies_binder_pred% $x $p ∧ $b)
  | `(∃! _ $p:binderPred, $b) => `(∃! x, satisfies_binder_pred% x $p ∧ $b)
end Unique

class One (α : Type u) where
  one : α


instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

variable {α : Type u}

instance (priority := 20) Zero.instNonempty [Zero α] : Nonempty α :=
  ⟨0⟩

instance (priority := 20) One.instNonempty [One α] : Nonempty α :=
  ⟨1⟩
