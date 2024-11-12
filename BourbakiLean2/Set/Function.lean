import BourbakiLean2.Set.Rel

variable {α β γ δ : Type*}

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

def is_constant (f : α → β) := ∀ a a', f a = f a'
@[simp] theorem Function.const_is_constant {a : α} : is_constant (Function.const β a) :=
  fun _ _ => rfl

def fixpoints (f : α → α) := {a | f a = a}
@[simp] theorem mem_fixpoints {f : α → α} {a : α} : a ∈ fixpoints f ↔ f a = a := Iff.rfl
@[simp] theorem fixpoints_id : fixpoints (@id α) = Set.univ := by
  ext
  simp only [mem_fixpoints, id_eq, Set.mem_univ]


end Function
