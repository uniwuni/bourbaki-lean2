import BourbakiLean2.Set.Rel
import BourbakiLean2.Logic

variable {α β γ δ : Type*} {f : α → β} {g : γ → α}

namespace Set
def image (f : α → β) (x : Set α) := (Relation.graph f).image x
def preimage (f : α → β) (x : Set β) := (Relation.graph f).preimage x
infixl:80 " '' " => image
infixl:80 " ⁻¹' " => preimage
@[simp] theorem mem_image_iff {x : Set α} {f : α → β} {b : β} : b ∈ image f x ↔ ∃ a, b = f a ∧ a ∈ x := Iff.rfl
@[simp] theorem mem_preimage_iff {y : Set β} {f : α → β} {a : α} : a ∈ preimage f y ↔ f a ∈ y := by
  simp only [preimage, Relation.mem_preimage_iff, Relation.mem_graph_iff, exists_eq_left]

end Set
namespace Function

def IsConstant (f : α → β) := ∀ a a', f a = f a'
@[simp] theorem Function.const_isConstant {a : α} : IsConstant (Function.const β a) :=
  fun _ _ => rfl

def fixpoints (f : α → α) := {a | f a = a}
@[simp] theorem mem_fixpoints {f : α → α} {a : α} : a ∈ fixpoints f ↔ f a = a := Iff.rfl
@[simp] theorem fixpoints_id : fixpoints (@id α) = Set.univ := by
  ext
  simp only [mem_fixpoints, id_eq, Set.mem_univ]

def is_extension {x : Set α} (g : α → β) (f : ↑ x → β) := ∀ a , f a = g a.1

@[simp] def restriction (f : α → β) (x : Set α) : ↑ x → β := fun a => f a.1

infixl:90 "|_" => restriction

@[simp] theorem is_extension_of_restriction {x : Set α} : is_extension f (f |_ x) := fun _ => rfl

@[simp] theorem restriction_id {x : Set α} : restriction id x = fun a => a.1 := rfl
@[simp] theorem restriction_const {x : Set α} {b : β}: restriction (const α b) x = const _ b := rfl
theorem restriction_comp {z : Set γ} {g : γ → α} : restriction (f ∘ g) z = f ∘ restriction g z := rfl


def Injective (f : α → β) := ∀ a a', f a = f a' → a = a'

theorem inj_iff_neq_of_neq : Injective f ↔ ∀ a a', a ≠ a' → f a ≠ f a' := by
  apply forall_congr'
  intro a
  apply forall_congr'
  intro a'
  rw[imp_iff_not_imp_not]

@[simp] theorem id_inj : Injective (id : α → α) := fun _ _ => id
theorem comp_inj_of_inj_inj (h : Injective f) (h' : Injective g) : Injective (f ∘ g) :=
  fun _ _' h'' => h' _ _ (h _ _ h'')

theorem inj_of_comp_inj (h : Injective (f ∘ g)) : Injective g :=
  fun _ _ h'' => h _ _ (congrArg f h'')

theorem restriction_inj_of_comp_inj (h : Injective (f ∘ g)) : Injective (f |_ (Set.image g Set.univ)) := by
  rintro ⟨a, ha⟩ ⟨a', ha'⟩ h'
  simp only [restriction, Subtype.mk.injEq] at *
  rw[Set.mem_image_iff] at ha ha'
  rcases ha with ⟨_, ha, _⟩
  rcases ha' with ⟨_, ha', _⟩
  rw[ha, ha'] at h' |-
  specialize h _ _ h'
  rw[h]

@[simp] theorem comp_self_inj_iff_inj {f : α → α}: Injective (f ∘ f) ↔ Injective f :=
  ⟨inj_of_comp_inj, fun h => comp_inj_of_inj_inj h h⟩

end Function
