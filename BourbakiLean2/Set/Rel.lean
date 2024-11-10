import BourbakiLean2.Set.Basic

abbrev Relation (α β : Type*) := Set (α × β)

namespace Relation
variable {α β : Type*}

def domain (r : Relation α β) : Set α := {a | ∃ b, (a,b) ∈ r}
def range (r : Relation α β) : Set β := {b | ∃ a, (a,b) ∈ r}

variable {r : Relation α β} {a : α} {b : β}

@[simp] theorem mem_domain_iff :
    a ∈ domain r ↔ ∃ b, (a,b) ∈ r := Iff.rfl

@[simp] theorem mem_range_iff :
    b ∈ range r ↔ ∃ a, (a,b) ∈ r := Iff.rfl

theorem mem_domain_of (h : (a,b) ∈ r) : a ∈ domain r := ⟨b, h⟩
theorem mem_range_of (h : (a,b) ∈ r) : b ∈ range r := ⟨a, h⟩

@[simp] theorem rel_subset_prod : r ⊆ (domain r).prod (range r) := by
  rintro ⟨a,b⟩ h
  simp only [Set.mem_prod_iff, mem_domain_iff, mem_range_iff]
  exact ⟨⟨b, h⟩, ⟨a,h⟩⟩

theorem rel_nonempty_iff_domain_and_range_nonempty :
    r.Nonempty ↔ r.domain.Nonempty ∧ r.range.Nonempty :=
  ⟨fun ⟨_, h⟩ => ⟨⟨_, mem_domain_of h⟩, ⟨_, mem_range_of h⟩⟩,
   fun ⟨⟨_, ⟨_, h⟩⟩, _⟩ => ⟨_,h⟩⟩

theorem rel_nonempty_of_domain_nonempty :
    r.domain.Nonempty → r.Nonempty
| ⟨_, ⟨_, h⟩⟩ => ⟨_,h⟩

theorem rel_nonempty_of_range_nonempty :
    r.range.Nonempty → r.Nonempty
| ⟨_, ⟨_, h⟩⟩ => ⟨_,h⟩

def image (r : Relation α β) (x : Set α) : Set β :=
  {b | ∃ a, (a,b) ∈ r ∧ a ∈ x}

def preimage (r : Relation α β) (y : Set β) : Set α :=
  {a | ∃ b, (a,b) ∈ r ∧ b ∈ y}

@[simp] theorem mem_image_iff {x : Set α}:
    b ∈ image r x ↔ ∃ a, (a,b) ∈ r ∧ a ∈ x := Iff.rfl

@[simp] theorem mem_preimage_iff {y : Set β}:
    a ∈ preimage r y ↔ ∃ b, (a,b) ∈ r ∧ b ∈ y := Iff.rfl

@[simp] theorem image_univ_range : r.image Set.univ = r.range := by
  ext a
  apply exists_congr
  intro _
  simp only [Set.mem_univ, and_true]

@[simp] theorem preimage_univ_domain : r.preimage Set.univ = r.domain := by
  ext a
  apply exists_congr
  intro _
  simp only [Set.mem_univ, and_true]

@[simp] theorem image_domain_range : r.image r.domain = r.range := by
  rw[← image_univ_range]
  unfold image
  ext b
  simp only [mem_domain_iff, Set.mem_setOf_iff, Set.mem_univ, and_true]
  exact exists_congr fun a => ⟨And.left, fun h => ⟨h, ⟨_,h⟩⟩⟩

@[simp] theorem preimage_range_domain : r.preimage r.range = r.domain := by
  rw[← preimage_univ_domain]
  unfold preimage
  ext a
  simp only [mem_range_iff, Set.mem_setOf_iff, Set.mem_univ, and_true]
  exact exists_congr fun a => ⟨And.left, fun h => ⟨h, ⟨_,h⟩⟩⟩

end Relation
