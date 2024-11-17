
variable {p q : Prop}
theorem imp_iff_not_imp_not : (p → q) ↔ (¬ q → ¬ p) := by
  constructor
  · exact fun h h' h'' => h' (h h'')
  · intro h h'
    by_cases h'' : q
    · exact h''
    · exact (h h'' h').elim

universe u v
theorem func_subsingleton_iff_to_empty {α : Type u} {β : Type v} (h : α → Empty) : Subsingleton (α → β) := by
  constructor
  intro a b
  ext c
  rcases h c
@[simp] theorem eq_rec_self {α : Sort u} {x : α → Sort u} {a} {h : a = a} {h' : x a} :
  @Eq.rec α a (fun x_1 _ ↦ x x_1) h' a h = h' := by
  rcases h
  rfl

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

-- Porting note:
-- This should not require a nolint,
-- but it is currently failing due to a problem in the linter discussed at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60simpNF.60.20error.20.22unknown.20metavariable.22
@[simp]
theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit :=
  rfl

/-- Every provable proposition is unique, as all proofs are equal. -/
def uniqueProp {p : Prop} (h : p) : Unique.{0} p where
  default := h
  uniq _ := rfl

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
