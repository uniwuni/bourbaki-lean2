import BourbakiLean2.Set.Basic

abbrev Relation (α β : Type*) := Set (α × β)

namespace Relation
variable {α β γ δ : Type*}

def domain (r : Relation α β) : Set α := {a | ∃ b, (a,b) ∈ r}
def range (r : Relation α β) : Set β := {b | ∃ a, (a,b) ∈ r}

variable {r r' : Relation α β} {s : Relation γ α} {t : Relation δ γ} {a : α} {b : β} {c : γ}

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

variable {x x' : Set α} {y y' : Set β} {z z' : Set γ}

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

/- SECTIONS -/

def sect (r : Relation α β) (a : α) := image r {a}

@[simp] theorem mem_sect_iff : b ∈ r.sect a ↔ (a,b) ∈ r := by
  simp only [sect, mem_image_iff, Set.mem_singleton_iff, exists_eq_right]

theorem rel_subset_iff_sect_subset : r ⊆ r' ↔ (∀ a, r.sect a ⊆ r'.sect a) := by
  constructor
  · intro h a b
    rw[mem_sect_iff, mem_sect_iff]
    exact @h (a,b)
  · rintro h ⟨a,b⟩ h'
    specialize @h a b
    rw[mem_sect_iff, mem_sect_iff] at *
    exact h h'

theorem sect_mono (h : r ⊆ r') : r.sect a ⊆ r'.sect a := by
  rw[rel_subset_iff_sect_subset] at h
  exact h a

/- INVERSE -/

def inv (r : Relation α β) : Relation β α := {p | (p.2, p.1) ∈ r}

@[simp] theorem mem_inv_iff : (b,a) ∈ r.inv ↔ (a,b) ∈ r := Iff.rfl

@[simp] theorem domain_inv : r.inv.domain = r.range := by
  simp only [domain, mem_inv_iff, range]

@[simp] theorem range_inv : r.inv.range = r.domain := by
  simp only [domain, mem_inv_iff, range]

@[simp] theorem image_inv : r.inv.image y = r.preimage y := by
  simp only [image, mem_inv_iff, preimage]

@[simp] theorem preimage_inv : r.inv.preimage x = r.image x := by
  simp only [image, mem_inv_iff, preimage]

@[simp] theorem inv_empty : (∅ : Relation α β).inv = ∅ := by
  ext a
  rcases a
  simp only [mem_inv_iff, Set.not_mem_empty]

@[simp] theorem inv_univ : Relation.inv (Set.univ : Relation α β) = Set.univ := by
  ext a
  rcases a
  simp only [mem_inv_iff, Set.mem_univ]

@[simp] theorem inv_inv : r.inv.inv = r := by
  ext a
  rcases a
  simp only [mem_inv_iff]

theorem inv_monotone (h : r ⊆ r') : r.inv ⊆ r'.inv := by
  rintro ⟨_,_⟩
  simp only [mem_inv_iff]
  apply h

/- SET PRODUCT SPECIAL CASES -/

@[simp] theorem sprod_domain (h : y.Nonempty) : Relation.domain (x.prod y) = x := by
  ext a
  simp only [mem_domain_iff, Set.mem_prod_iff, exists_and_left, and_iff_left_iff_imp]
  intro
  assumption

@[simp] theorem sprod_range (h : x.Nonempty) : Relation.range (x.prod y) = y := by
  ext a
  simp only [mem_range_iff, Set.mem_prod_iff, exists_and_right, and_iff_right_iff_imp]
  intro
  assumption

@[simp] theorem sprod_image (h : a ∈ x) (h' : a ∈ x') : Relation.image (x.prod y) x' = y := by
  ext b'
  simp only [mem_image_iff, Set.mem_prod_iff]
  refine ⟨fun ⟨_, ⟨⟨_, v⟩,_⟩⟩ => v,
          fun h'' => ⟨a, ⟨⟨h,h''⟩,h'⟩⟩⟩

@[simp] theorem sprod_preimage (h : b ∈ y) (h' : b ∈ y') : Relation.preimage (x.prod y) y' = x := by
  ext a'
  simp only [mem_preimage_iff, Set.mem_prod_iff]
  refine ⟨fun ⟨_, ⟨⟨v, _⟩,_⟩⟩ => v,
          fun h'' => ⟨b, ⟨⟨h'',h⟩,h'⟩⟩⟩

@[simp] theorem sprod_inv : Relation.inv (x.prod y) = y.prod x := by
  ext ⟨a,b⟩
  simp only [mem_inv_iff, Set.mem_prod_iff, and_comm]

@[simp] theorem sprod_sect (h : a ∈ x) : Relation.sect (x.prod y) a = y := by
  apply sprod_image h
  simp only [Set.mem_singleton_iff]

/- COMPOSITION -/

def comp (r : Relation α β) (s : Relation γ α) : Relation γ β :=
  {x | ∃ a, ⟨x.1, a⟩ ∈ s ∧ ⟨a, x.2⟩ ∈ r}

local infixr:80 " ∘ " => Relation.comp

@[simp] theorem mem_comp_iff : (c,b) ∈ r ∘ s ↔ (∃ a, (c,a) ∈ s ∧ (a,b) ∈ r) := Iff.rfl

theorem mem_comp_of (h : (c,a) ∈ s) (h' : (a,b) ∈ r) : (c,b) ∈ r ∘ s :=
  mem_comp_iff.mpr ⟨a, ⟨h,h'⟩⟩

/- EDGE CASES -/

@[simp] theorem comp_empty : r ∘ (∅ : Relation γ α) = ∅ := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.not_mem_empty, false_and, exists_false]

@[simp] theorem empty_comp : (∅ : Relation α β) ∘ s = ∅ := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.not_mem_empty, and_false, exists_false]

@[simp] theorem comp_univ : r ∘ (Set.univ : Relation γ α) = Set.univ.prod r.range := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.mem_univ, true_and, Set.mem_prod_iff, mem_range_iff]

@[simp] theorem univ_comp : (Set.univ : Relation α β) ∘ s = s.domain.prod Set.univ := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.mem_univ, and_true, Set.mem_prod_iff, mem_domain_iff]

/- COMP PROPS -/

@[simp] theorem inv_comp : (r ∘ s).inv = s.inv ∘ r.inv := by
  ext ⟨_,_⟩
  simp only [mem_inv_iff, mem_comp_iff, and_comm]

@[simp] theorem comp_assoc : r ∘ (s ∘ t) = (r ∘ s) ∘ t := by
  ext ⟨d,b⟩
  exact ⟨fun ⟨a, ⟨⟨c, ⟨h',h''⟩⟩, h⟩⟩ => ⟨c, ⟨h',⟨a,⟨h'',h⟩⟩⟩⟩,
         fun ⟨c, ⟨h',⟨a,⟨h'',h⟩⟩⟩⟩ => ⟨a, ⟨⟨c, ⟨h',h''⟩⟩, h⟩⟩⟩

end Relation
