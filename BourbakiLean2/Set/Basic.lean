import BourbakiLean2.Set.Defs

namespace Set
variable {α : Type*} {p q : α → Prop}

/- setOf stuff -/

@[simp]
theorem mem_setOf_iff {x : α} :
    x ∈ {y | p y} ↔ p x := Iff.rfl
theorem mem_setOf_of {x : α} (h : p x) : x ∈ {y | p y} := h
theorem of_mem_setOf {x : α} (h : x ∈ {y | p y}) : p x := h

/- subsets -/
@[simp]
theorem subset_refl (x : Set α) : x ⊆ x := fun _ h => h

section
variable {x y z : Set α}

@[ext] theorem eq_of_mem_iff_mem (h : ∀ a, a ∈ x ↔ a ∈ y) : x = y :=
  Set.ext h
theorem subset_rfl : x ⊆ x := subset_refl x
theorem subset_trans (h : x ⊆ y) (h' : y ⊆ z) : x ⊆ z :=
  fun _ h'' => h' (h h'')
theorem subset_antisym (h : x ⊆ y) (h' : y ⊆ x) : x = y := ext (fun x => ⟨@h x, @h' x⟩)

theorem eq_iff_subset_subset : x = y ↔ (x ⊆ y ∧ y ⊆ x) := by
  constructor
  · intro h
    simp only [h, subset_refl, and_self]
  · rintro ⟨h, h'⟩
    exact subset_antisym h h'

@[simp] theorem setOf_subset_iff : {y | p y} ⊆ x ↔ (∀ a, p a → a ∈ x) := Iff.rfl
@[simp] theorem subset_setOf_iff : x ⊆ {y | p y} ↔ (∀ a, a ∈ x → p a) := Iff.rfl
@[simp] theorem setOf_subset_setOf_iff : {y | p y} ⊆ {y | q y} ↔ (∀ a, p a → q a) :=
  Iff.rfl
@[simp] theorem setOf_eq_setOf_iff : {y | p y} = {y | q y} ↔ (∀ a, p a ↔ q a) := by
  simp only [eq_iff_subset_subset, subset_setOf_iff, mem_setOf_iff]
  constructor
  · intro h a
    exact ⟨h.1 a, h.2 a⟩
  · intro h
    exact ⟨fun a => (h a).1, fun a => (h a).2⟩

/- simp lemmas -/

@[simp] theorem mem_univ {a : α} : a ∈ Set.univ := ⟨⟩
@[simp] theorem subset_univ : x ⊆ Set.univ := fun _ _ => ⟨⟩
@[simp] theorem not_mem_empty {a : α} : a ∉ (∅ : Set α) := fun x => x
@[simp] theorem empty_subset : ∅ ⊆ x := fun _ => False.elim
@[simp] theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl

end

/- sets of products -/

section
variable {β : Type*}

def prod (x : Set α) (y : Set β) : Set (α × β) := {a | a.1 ∈ x ∧ a.2 ∈ y}

@[simp] theorem mem_prod_iff {a : α} {b : β} {x : Set α} {y : Set β} :
    (a,b) ∈ prod x y ↔ a ∈ x ∧ b ∈ y := Iff.rfl

@[simp] theorem prod_subset_prod_nonempty_iff {x x' : Set α} {y y' : Set β}
    (hx : x.Nonempty) (hy : y.Nonempty) : prod x y ⊆ prod x' y' ↔ (x ⊆ x' ∧ y ⊆ y') := by
  rcases hx with ⟨ax, hx⟩
  rcases hy with ⟨ay, hy⟩
  constructor
  · intro h
    constructor
    · intro a h2
      specialize @h (a, ay)
      simp only [mem_prod_iff, and_self, forall_const, h2, hy] at h
      exact h.1
    · intro a h2
      specialize @h (ax, a)
      simp only [mem_prod_iff, and_self, forall_const, hx, h2] at h
      exact h.2
  · rintro ⟨h1, h2⟩ ⟨a,b⟩ h
    exact ⟨h1 h.1, h2 h.2⟩

@[simp] theorem prod_empty_iff {x : Set α} {y : Set β} :
    (prod x y).Nonempty ↔ (x.Nonempty ∧ y.Nonempty) := by
  simp only [Set.Nonempty, Prod.exists,  mem_prod_iff, exists_and_left, exists_and_right]

end

end Set

def ExistsUnique {α : Type*} (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x
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
