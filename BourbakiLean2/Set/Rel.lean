import BourbakiLean2.Set.Basic

abbrev Relation (α β : Type*) := Set (α × β)
variable {α β γ δ : Type*}
namespace Relation


def domain (r : Relation α β) : Set α := {a | ∃ b, (a,b) ∈ r}
def range (r : Relation α β) : Set β := {b | ∃ a, (a,b) ∈ r}

variable {r r' : Relation α β} {s s' : Relation γ α} {t : Relation δ γ} {a a' : α} {b : β} {c : γ}

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

theorem range_comp_subset : (r ∘ s).range ⊆ r.range := by
  intro
  simp only [mem_range_iff, mem_comp_iff, forall_exists_index, and_imp]
  exact fun _ _ _ h' => ⟨_, h'⟩

theorem domain_comp_subset : (r ∘ s).domain ⊆ s.domain := by
  intro
  simp only [mem_domain_iff, mem_comp_iff, forall_exists_index, and_imp]
  exact fun _ _ h _ => ⟨_, h⟩

theorem range_comp_eq_image : (r ∘ s).range = r.image s.range := by
  ext b
  simp only [mem_range_iff, mem_comp_iff, mem_image_iff]
  exact ⟨fun ⟨_,⟨_,⟨h,h'⟩⟩⟩ => ⟨_,⟨h',⟨_,h⟩⟩⟩,
         fun ⟨_,⟨h',⟨_,h⟩⟩⟩ => ⟨_,⟨_,⟨h,h'⟩⟩⟩⟩

theorem range_domain_eq_preimage : (r ∘ s).domain = s.preimage r.domain := by
  ext c
  simp only [mem_domain_iff, mem_comp_iff, mem_preimage_iff]
  exact ⟨fun ⟨_,⟨_,⟨h,h'⟩⟩⟩ => ⟨_,⟨h,⟨_,h'⟩⟩⟩,
         fun ⟨_,⟨h',⟨_,h⟩⟩⟩ => ⟨_,⟨_,⟨h',h⟩⟩⟩⟩

theorem comp_mono_left (h : r ⊆ r') : r ∘ s ⊆ r' ∘ s := by
  intro ⟨_,_⟩
  simp only [mem_comp_iff, forall_exists_index, and_imp] at *
  exact fun x h' h'' => ⟨_,⟨h', h h''⟩⟩

theorem comp_mono_right (h : s ⊆ s') : r ∘ s ⊆ r ∘ s' := by
  intro ⟨_,_⟩
  simp only [mem_comp_iff, forall_exists_index, and_imp] at *
  exact fun x h' h'' => ⟨_,⟨h h', h''⟩⟩

theorem comp_mono (h : r ⊆ r') (h' : s ⊆ s') : r ∘ s ⊆ r' ∘ s' := by
  intro ⟨_,_⟩
  simp only [mem_comp_iff, forall_exists_index, and_imp] at *
  exact fun x h'' h''' => ⟨_,⟨h' h'', h h'''⟩⟩

theorem subset_preimage_image_of_subset_domain (h : x ⊆ r.domain) : x ⊆ r.preimage (r.image x) := by
  intro a h'
  specialize h h'
  simp only [mem_domain_iff, mem_preimage_iff, mem_image_iff] at *
  rcases h with ⟨b, h''⟩
  exact ⟨b, ⟨h'', ⟨_, ⟨h'',h'⟩⟩⟩⟩

theorem subset_image_preimage_of_subset_range (h : y ⊆ r.range): y ⊆ r.image (r.preimage y) := by
  intro b h'
  specialize h h'
  simp only [mem_range_iff, mem_image_iff, mem_preimage_iff] at *
  rcases h with ⟨a, h''⟩
  exact ⟨a,⟨h'',b,h'',h'⟩⟩

@[simp] theorem image_comp : (r ∘ s).image z = r.image (s.image z) := by
  ext b
  simp only [mem_image_iff, mem_comp_iff]
  exact ⟨fun ⟨c,⟨⟨a,⟨h,h'⟩⟩,h''⟩⟩ => ⟨_,h',_,h,h''⟩,
         fun ⟨a,h',c,h,h''⟩ => ⟨c,⟨a,h,h'⟩,h''⟩⟩

@[simp] theorem preimage_comp : (r ∘ s).preimage y = s.preimage (r.preimage y) := by
  rw[←image_inv, ←image_inv, ←image_inv, inv_comp, image_comp]


/- DIAGONAL -/

def diag : Relation α α := {x | x.1 = x.2}

@[simp] theorem mem_diag_iff : (a,a') ∈ diag ↔ a = a' := Iff.rfl

@[simp] theorem image_diag : diag.image x = x := by
  ext _
  simp only [mem_image_iff, mem_diag_iff, exists_eq_left]

@[simp] theorem preimage_diag : diag.preimage x = x := by
  ext _
  simp only [mem_preimage_iff, mem_diag_iff, exists_eq_left']

@[simp] theorem range_diag : diag.range = @Set.univ α := by
  ext _
  simp only [mem_range_iff, mem_diag_iff, exists_eq, Set.mem_univ]

@[simp] theorem domain_diag : diag.domain = @Set.univ α := by
  ext _
  simp only [mem_domain_iff, mem_diag_iff, exists_eq', Set.mem_univ]

@[simp] theorem inv_diag : diag.inv = (diag : Relation α α) := by
  ext ⟨_,_⟩
  simp only [mem_inv_iff, mem_diag_iff, Eq.comm]

@[simp] theorem diag_comp : diag ∘ r = r := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, mem_diag_iff, exists_eq_right]

@[simp] theorem comp_diag : r ∘ diag = r := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, mem_diag_iff, exists_eq_left']

/- FUNCTIONAL -/

def Functional (r : Relation α β) := ∀ x, ∃! y, ⟨x,y⟩ ∈ r
def graph (f : α → β) : Relation α β := {x | x.2 = f x.1}

variable {f : α → β}

@[simp] theorem mem_graph_iff : ⟨a, b⟩ ∈ graph f ↔ b = f a := by
  simp only [graph, Set.mem_setOf_iff]

@[simp] theorem mem_graph : ⟨a, f a⟩ ∈ graph f := by rw[mem_graph_iff]

@[simp] theorem graph_functional : Functional (graph f) := by
  intro x
  exists f x
  simp only [mem_graph_iff, imp_self, implies_true, and_self]

@[simp] theorem functional_iff_graph : Functional r ↔ (∃ f, r = graph f) := by
  constructor
  · intro h
    have ⟨f, h'⟩ := Classical.axiomOfChoice h
    exists f
    ext ⟨a,b⟩
    specialize h' a
    simp only at h'
    rcases h' with ⟨h', h''⟩
    constructor
    · intro h'''
      specialize h'' b h'''
      simp only [h'', mem_graph_iff]
    · intro h'''
      simp only [mem_graph_iff] at h'''
      rw[h''']
      exact h'
  · rintro ⟨f, rfl⟩
    simp only [graph_functional]

@[simp] theorem graph_section : (graph f).sect a = {f a} := by
  ext
  simp only [mem_sect_iff, mem_graph_iff, Set.mem_singleton_iff]

theorem diag_graph_id : diag = (graph (@id α)) := by
  ext ⟨a,b⟩
  simp only [mem_diag_iff, mem_graph_iff, id_eq, eq_comm]

theorem diag_functional : Functional (@diag α) := by
  rw[diag_graph_id]
  apply graph_functional

theorem graph_comp {g : γ → α} : graph (f ∘ g) = (graph f) ∘ (graph g) := by
  ext ⟨c,b⟩
  simp only [mem_graph_iff, Function.comp_apply, mem_comp_iff, exists_eq_left]

theorem functional_comp_of_functional (h : Functional r) (h' : Functional s) : Functional (r ∘ s) := by
  rw[functional_iff_graph] at *
  obtain ⟨f, h⟩ := h
  obtain ⟨g, h'⟩ := h'
  exists f ∘ g
  rw[graph_comp, h, h']

@[simp] theorem domain_graph : (graph f).domain = Set.univ := by
  ext a
  simp only [mem_domain_iff, mem_graph_iff, exists_eq, Set.mem_univ]

theorem domain_functional (h : Functional r) : r.domain = Set.univ := by
  rw[functional_iff_graph] at h
  obtain ⟨f,rfl⟩ := h
  simp only [domain_graph]


def inverse_image {γ : Type*} (r : Relation α α) (f : γ → α) : Relation γ γ :=
  fun ⟨x,y⟩ => r ⟨f x, f y⟩

@[simp] theorem mem_inverse_image_iff {r : Relation α α} {f : γ → α} {c c' : γ} :
  ⟨c,c'⟩ ∈ r.inverse_image f ↔ ⟨f c, f c'⟩ ∈ r := Iff.rfl

def restrict (r : Relation α α) (x : Set α) : Relation x x :=
  fun ⟨a,b⟩ => r ⟨a,b⟩

@[simp] theorem mem_restrict_iff {r : Relation α α} {x : Set α} {a a' : x} :
    ⟨a,a'⟩ ∈ r.restrict x ↔ ⟨a,a'⟩ ∈ r := Iff.rfl

theorem restrict_inverse_image {r : Relation α α} {x : Set α} :
    r.restrict x = r.inverse_image Subtype.val := by
  ext ⟨a,b⟩
  simp only [mem_restrict_iff, mem_inverse_image_iff]

theorem injection_restrict_compatible {r : Relation α α} {x : Set α} (a a' : x)
    (h : ⟨a,a'⟩ ∈ r.restrict x) : ⟨Subtype.val a, Subtype.val a'⟩ ∈ r :=
  Relation.mem_restrict_iff.mp h

def prod_rel (r : Relation α α) (s : Relation β β) : Relation (α × β) (α × β) :=
  fun ⟨⟨a,b⟩, ⟨a',b'⟩⟩ => ⟨a, a'⟩ ∈ r ∧ ⟨b, b'⟩ ∈ s

@[simp] theorem mem_prod_rel_iff {r : Relation α α} {s : Relation β β} {a a' b b'} :
    ⟨⟨a,b⟩, ⟨a',b'⟩⟩ ∈ r.prod_rel s ↔ ⟨a, a'⟩ ∈ r ∧ ⟨b, b'⟩ ∈ s := Iff.rfl
end Relation
