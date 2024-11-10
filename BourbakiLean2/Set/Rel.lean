import BourbakiLean2.Set.Basic

abbrev Relation (α β : Type*) := Set (α × β)

namespace Relation
variable {α β : Type*}

def domain (r : Relation α β) : Set α := {a | ∃ b, (a,b) ∈ r}
def range (r : Relation α β) : Set β := {b | ∃ a, (a,b) ∈ r}

variable {r r' : Relation α β} {a : α} {b : β}

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

/- NONEMPTINESS -/
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

/- IMAGE PREIMAGE -/
def image (r : Relation α β) (x : Set α) : Set β :=
  {b | ∃ a, (a,b) ∈ r ∧ a ∈ x}

def preimage (r : Relation α β) (y : Set β) : Set α :=
  {a | ∃ b, (a,b) ∈ r ∧ b ∈ y}

variable {x x' : Set α} {y y' : Set β}

@[simp] theorem mem_image_iff :
    b ∈ image r x ↔ ∃ a, (a,b) ∈ r ∧ a ∈ x := Iff.rfl

@[simp] theorem mem_preimage_iff :
    a ∈ preimage r y ↔ ∃ b, (a,b) ∈ r ∧ b ∈ y := Iff.rfl

/- EDGE CASES -/

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

/- BORING EMPTY STUFF -/
@[simp] theorem image_empty : r.image ∅ = ∅ := by
  ext
  simp only [mem_image_iff, Set.not_mem_empty, and_false, exists_false]

@[simp] theorem preimage_empty : r.preimage ∅ = ∅ := by
  ext
  simp only [mem_preimage_iff, Set.not_mem_empty, and_false, exists_false]

@[simp] theorem image_empty_rel : Relation.image ∅ x = (∅ : Set β) := by
  ext
  simp only [mem_image_iff, Set.not_mem_empty, false_and, exists_false]

@[simp] theorem preimage_empty_rel : Relation.preimage ∅ y = (∅ : Set α) := by
  ext
  simp only [mem_preimage_iff, Set.not_mem_empty, false_and, exists_false]

@[simp] theorem range_empty_rel : Relation.range (∅ : Relation α β) = ∅ := by
  ext
  simp only [mem_range_iff, Set.not_mem_empty, exists_false]

@[simp] theorem domain_empty_rel : Relation.domain (∅ : Relation α β) = ∅ := by
  ext
  simp only [mem_domain_iff, Set.not_mem_empty, exists_false]

/- BORING UNIV STUFF -/

@[simp] theorem image_univ_rel (h : x.Nonempty) :
    Relation.image (Set.univ : Relation α β) x = Set.univ := by
  ext
  simpa only [mem_image_iff, Set.mem_univ, true_and, iff_true]

@[simp] theorem preimage_univ_rel (h : y.Nonempty) :
    Relation.preimage (Set.univ : Relation α β) y = Set.univ := by
  ext
  simpa only [mem_preimage_iff, Set.mem_univ, true_and, iff_true]

@[simp] theorem range_univ_rel [h : Nonempty α] : Relation.range (Set.univ : Relation α β) = Set.univ := by
  ext
  simp only [mem_range_iff, Set.mem_univ, exists_const]

@[simp] theorem domain_univ_rel [h : Nonempty β] : Relation.domain (Set.univ : Relation α β) = Set.univ := by
  ext
  simp only [mem_domain_iff, Set.mem_univ, exists_const]

/- MONOTONY -/

theorem image_mono_left (h : r ⊆ r') : r.image x ⊆ r'.image x := by
  intro b
  simp only [mem_image_iff, forall_exists_index, and_imp] at *
  exact fun a h' h'' => ⟨a, ⟨h h', h''⟩⟩

theorem image_mono_right (h : x ⊆ x') : r.image x ⊆ r.image x' := by
  intro b
  simp only [mem_image_iff, forall_exists_index, and_imp]
  exact fun a h' h'' => ⟨a, ⟨h', h h''⟩⟩

theorem image_mono (h : r ⊆ r') (h' : x ⊆ x') : r.image x ⊆ r'.image x' :=
  Set.subset_trans (image_mono_left h) (image_mono_right h')

theorem preimage_mono_left (h : r ⊆ r') : r.preimage y ⊆ r'.preimage y := by
  intro b
  simp only [mem_preimage_iff, forall_exists_index, and_imp]
  exact fun a h' h'' => ⟨a, ⟨h h', h''⟩⟩

theorem preimage_mono_right (h : y ⊆ y') : r.preimage y ⊆ r.preimage y' := by
  intro b
  simp only [mem_preimage_iff, forall_exists_index, and_imp]
  exact fun a h' h'' => ⟨a, ⟨h', h h''⟩⟩

theorem preimage_mono (h : r ⊆ r') (h' : y ⊆ y') : r.preimage y ⊆ r'.preimage y' :=
  Set.subset_trans (preimage_mono_left h) (preimage_mono_right h')

theorem range_mono (h : r ⊆ r') : r.range ⊆ r'.range := by
  rw[← image_univ_range, ← image_univ_range]
  apply image_mono_left h

theorem domain_mono (h : r ⊆ r') : r.domain ⊆ r'.domain := by
  rw[← preimage_univ_domain, ← preimage_univ_domain]
  apply preimage_mono_left h

/- MONOTONY CONSEQUENCES -/

@[simp] theorem image_subset_range : r.image x ⊆ r.range := by
  rw[← image_univ_range]
  apply image_mono_right Set.subset_univ

@[simp] theorem preimage_subset_domain : r.preimage y ⊆ r.domain := by
  rw[← preimage_univ_domain]
  apply preimage_mono_right Set.subset_univ

theorem image_of_domain_subset (h : r.domain ⊆ x) : r.image x = r.range := by
  apply Set.subset_antisym
  · rw[← image_univ_range]
    apply image_mono_right Set.subset_univ
  · rw[← image_domain_range]
    apply image_mono_right h

theorem preimage_of_range_subset (h : r.range ⊆ y) : r.preimage y = r.domain := by
  apply Set.subset_antisym
  · rw[← preimage_univ_domain]
    apply preimage_mono_right Set.subset_univ
  · rw[← preimage_range_domain]
    apply preimage_mono_right h

end Relation
