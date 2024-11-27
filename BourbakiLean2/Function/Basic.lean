import BourbakiLean2.Set.Rel
import BourbakiLean2.Logic

variable {α β γ δ : Type*} {f : α → β} {g : γ → α}

namespace Set
/- func image preimage -/

def image (f : α → β) (x : Set α) := (Relation.graph f).image x
def preimage (f : α → β) (x : Set β) := (Relation.graph f).preimage x

infixl:80 " '' " => image
infixl:80 " ⁻¹' " => preimage
@[simp] theorem mem_image_iff {x : Set α} {f : α → β} {b : β} : b ∈ image f x ↔ ∃ a, b = f a ∧ a ∈ x := Iff.rfl
@[simp] theorem mem_preimage_iff {y : Set β} {f : α → β} {a : α} : a ∈ preimage f y ↔ f a ∈ y := by
  simp only [preimage, Relation.mem_preimage_iff, Relation.mem_graph_iff, exists_eq_left]
theorem val_mem_image_of_mem {x : Set α} {f : α → β} {a : α} (h : a ∈ x) : f a ∈ f '' x := by
  simp only [mem_image_iff]
  exists a
@[simp high] theorem val_mem_image_univ {f : α → β} {a : α} : f a ∈ f '' Set.univ :=
  val_mem_image_of_mem mem_univ
end Set
namespace Function

@[simp] theorem image_singleton {f : α → β} {a} : f '' {a} = {f a} := by
  ext b
  simp only [Set.mem_image_iff, Set.mem_singleton_iff, exists_eq_right]

@[simp] theorem comp_assoc {h : δ → γ}: f ∘ (g ∘ h) = (f ∘ g) ∘ h := by
  ext
  rfl

@[simp] theorem comp_id_left : id ∘ f = f := by
  ext
  rfl

@[simp] theorem comp_id_right : f ∘ id = f := by
  ext
  rfl

@[simp] theorem subset_preimage_image {x : Set α} : x ⊆ f ⁻¹' (f '' x) := by
  intro a h
  simp only [Set.mem_preimage_iff, Set.mem_image_iff]
  exists a

@[simp] theorem image_preimage_subset {y : Set β} : f '' (f ⁻¹' y) ⊆ y := by
  intro a h
  simp only [Set.mem_image_iff, Set.mem_preimage_iff] at h
  obtain ⟨_,rfl,h⟩ := h
  exact h

@[simp] theorem image_empty : f '' ∅ = ∅ := by
  ext a
  simp only [Set.mem_image_iff, Set.not_mem_empty, and_false, exists_false]

@[simp] theorem image_empty_iff_empty {x : Set α} : f '' x = ∅ ↔ x = ∅ := by
  constructor
  · intro h
    ext a
    simp only [Set.not_mem_empty, iff_false]
    intro h'
    have h' : f a ∈ f '' x := Set.val_mem_image_of_mem h'
    rw[h] at h'
    exact h'
  · rintro rfl
    exact image_empty

@[simp] theorem preimage_empty : f ⁻¹' ∅ = ∅ := by
  ext a
  simp only [Set.mem_preimage_iff, Set.not_mem_empty]

@[simp] theorem preimage_univ : f ⁻¹' Set.univ = Set.univ := by
  ext a
  simp only [Set.mem_preimage_iff, Set.mem_univ]

@[simp] theorem image_comp {z : Set γ} : (f ∘ g) '' z = f '' (g '' z) := by
  ext b
  simp only [Set.mem_image_iff, comp_apply]
  constructor
  · rintro ⟨c,rfl,h'⟩
    exact ⟨g c, rfl, c, rfl, h'⟩
  · rintro ⟨a, rfl, c, rfl, h''⟩
    exists c

@[simp] theorem preimage_comp {x} : (f ∘ g) ⁻¹' x = g ⁻¹' (f ⁻¹' x) := by
  ext a
  simp only [Set.mem_preimage_iff, comp_apply]

/- const -/
def IsConstant (f : α → β) := ∀ a a', f a = f a'
@[simp] theorem Function.const_isConstant {a : α} : IsConstant (Function.const β a) :=
  fun _ _ => rfl


/- fixpoints -/
def fixpoints (f : α → α) := {a | f a = a}
@[simp] theorem mem_fixpoints {f : α → α} {a : α} : a ∈ fixpoints f ↔ f a = a := Iff.rfl
@[simp] theorem fixpoints_id : fixpoints (@id α) = Set.univ := by
  ext
  simp only [mem_fixpoints, id_eq, Set.mem_univ]
theorem fixpoints_subset_comp_self {f : α → α}: fixpoints f ⊆ fixpoints (f ∘ f) := by
  intro a h
  simp only [mem_fixpoints, comp_apply] at *
  rw[h, h]

/- extension restriction -/

def is_extension {x : Set α} (g : α → β) (f : ↑ x → β) := ∀ a , f a = g a.1

@[simp] def restriction (f : α → β) (x : Set α) : ↑ x → β := fun a => f a.1
infixl:90 "|_" => restriction
@[simp] theorem is_extension_of_restriction {x : Set α} : is_extension f (f |_ x) := fun _ => rfl
@[simp] theorem restriction_id {x : Set α} : restriction id x = fun a => a.1 := rfl
@[simp] theorem restriction_const {x : Set α} {b : β}: restriction (const α b) x = const _ b := rfl
theorem restriction_comp {z : Set γ} {g : γ → α} : restriction (f ∘ g) z = f ∘ restriction g z := rfl

/- injectivity -/

@[simp] def Injective (f : α → β) := ∀ a a', f a = f a' → a = a'

theorem Injective.eq_iff (h : Injective f) {a a' : α} : f a = f a' ↔ a = a' :=
  ⟨h _ _, congrArg f⟩

theorem inj_iff_neq_of_neq : Injective f ↔ ∀ a a', a ≠ a' → f a ≠ f a' := by
  apply forall_congr'
  intro a
  apply forall_congr'
  intro a'
  rw[imp_iff_not_imp_not]

theorem Injective.comp (h : Injective f) (h' : Injective g) : Injective (f ∘ g) :=
  fun _ _' h'' => h' _ _ (h _ _ h'')

theorem inj_of_comp_inj (h : Injective (f ∘ g)) : Injective g :=
  fun _ _ h'' => h _ _ (congrArg f h'')

theorem inj_iff_preimage_eq :
    Injective f ↔ ∀ b, ∀ a a', a ∈ Set.preimage f {b} → a' ∈ Set.preimage f {b} → a = a' := by
  simp only [Injective, Set.mem_preimage_iff, Set.mem_singleton_iff]
  constructor
  · intro h b a a' h' h''
    rw[← h''] at h'
    exact h _ _ h'
  · intro h a a' h'
    exact h _ _ _ h' rfl

theorem restriction_inj_of_comp_inj (h : Injective (f ∘ g)) : Injective (f |_ (Set.image g Set.univ)) := by
  rintro ⟨a, ha⟩ ⟨a', ha'⟩ h'
  simp only [restriction, Subtype.mk.injEq] at *
  rw[Set.mem_image_iff] at ha ha'
  rcases ha with ⟨_, ha, _⟩
  rcases ha' with ⟨_, ha', _⟩
  rw[ha, ha'] at h' |-
  specialize h _ _ h'
  rw[h]


@[simp] theorem inj_id : Injective (id : α → α) := fun _ _ => id
@[simp] theorem comp_self_inj_iff_inj {f : α → α}: Injective (f ∘ f) ↔ Injective f :=
  ⟨inj_of_comp_inj, fun h => h.comp h⟩

theorem Injective.restriction (h : Injective f) {x : Set α} : Injective (f |_ x) := by
  rintro ⟨a, h'⟩ ⟨a', h''⟩ h'''
  simp only [Function.restriction] at h'''
  simp only [Subtype.mk.injEq]
  exact h _ _ h'''

theorem Injective.preimage_image (h : Injective f) {x : Set α} : Set.preimage f (Set.image f x) = x := by
  rw[Set.eq_iff_subset_subset,]
  constructor
  · intro a h'
    simp only [Set.mem_preimage_iff, Set.mem_image_iff] at h'
    obtain ⟨a', h', h''⟩ := h'
    rw[h _ _ h']
    exact h''
  · exact subset_preimage_image

/- surjectivity -/

def Surjective (f : α → β) := Set.image f Set.univ = Set.univ

@[simp] theorem surj_iff : Surjective f ↔ ∀ b, ∃a, b = f a := by
  simp only [Surjective, Set.ext_iff, Set.mem_image_iff, Set.mem_univ, and_true, iff_true]

theorem Surjective.exists_preimage (h : Surjective f) (b : β) : ∃a, b = f a :=
  surj_iff.mp h _

theorem Surjective.comp (h : Surjective f) (h' : Surjective g) : Surjective (f ∘ g) := by
  simp only [surj_iff, comp_apply] at *
  intro b
  obtain ⟨a, h⟩ := h b
  obtain ⟨c, h'⟩ := h' a
  exists c
  rw[h,h']

theorem surj_of_comp_surj (h : Surjective (f ∘ g)) : Surjective f := by
  simp only [surj_iff, comp_apply] at *
  intro b
  obtain ⟨a, h⟩ := h b
  exists g a

theorem surj_iff_preimage_nonempty : Surjective f ↔ ∀ b, (Set.preimage f {b}).Nonempty := by
  simp only [surj_iff]
  constructor
  · intro h b
    obtain ⟨a,rfl⟩ := h b
    exists a
    simp only [Set.mem_preimage_iff, Set.mem_singleton_iff]
  · intro h b
    obtain ⟨a,h⟩ := h b
    simp only [Set.mem_preimage_iff, Set.mem_singleton_iff] at h
    exists a
    rw[h]

theorem surj_iff_empty_of_preimage_empty : Surjective f ↔ ∀ y, Set.preimage f y = ∅ → y = ∅ := by
  simp only [surj_iff]
  constructor
  · intro h y
    rw[imp_iff_not_imp_not, ← ne_eq, ← Set.nonempty_iff_neq_empty, ← ne_eq, ← Set.nonempty_iff_neq_empty]
    intro ⟨b,h'⟩
    obtain ⟨a,rfl⟩ := h b
    exists a
    simp[h']
  · intro h b
    specialize h {b}
    simp only [Set.singleton_neq_empty, imp_false] at h
    rw[← ne_eq, ← Set.nonempty_iff_neq_empty] at h
    obtain ⟨a,h⟩ := h
    exists a
    simp only [Set.mem_preimage_iff, Set.mem_singleton_iff] at h
    exact h.symm

@[simp] theorem surj_id : Surjective (id : α → α) := surj_iff.mpr fun a => ⟨a, rfl⟩

@[simp] theorem comp_self_surj_iff_surj {f : α → α}: Surjective (f ∘ f) ↔ Surjective f :=
  ⟨surj_of_comp_surj, fun h => h.comp h⟩

theorem surjective_of_restriction {x : Set α} (h : Surjective (f |_ x)) : Surjective f := by
  simp only [surj_iff, restriction, Subtype.exists, exists_prop] at *
  intro b
  obtain ⟨a,_,h⟩ := h b
  exact ⟨a,h⟩

theorem Surjective.image_preimage (h : Surjective f) {y : Set β} : Set.image f (Set.preimage f y) = y := by
  rw[Set.eq_iff_subset_subset]
  constructor
  · simp only [image_preimage_subset]
  · intro b h'
    simp only [Set.mem_image_iff, Set.mem_preimage_iff]
    obtain ⟨a,h⟩ := h.exists_preimage b
    rw[h] at h'
    exists a

/- corestrictions -/

def corestrict (f : α → β) {y : Set β} (h : f '' Set.univ ⊆ y) : α → ↑ y :=
  fun a => ⟨f a, h (by simp only [Set.val_mem_image_univ])⟩

theorem corestrict_surjective : Surjective (corestrict f (Set.subset_refl _)) := by
  simp only [surj_iff, Subtype.forall, Set.mem_image_iff, Set.mem_univ, and_true,
    forall_exists_index]
  rintro x a rfl
  exists a

@[simp] theorem coe_corestrict {y : Set β} {h : f '' Set.univ ⊆ y} {a : α} :
    ↑ (corestrict f h a) = f a := rfl

/- bijectivity -/

def Bijective (f : α → β) := Injective f ∧ Surjective f

theorem Bijective.inj (h : Bijective f) : Injective f := h.1
theorem Bijective.surj (h : Bijective f) : Surjective f := h.2
theorem bij_id : Bijective (id : α → α) := ⟨inj_id, surj_id⟩
theorem Bijective.comp (h : Bijective f) (h' : Bijective g) : Bijective (f ∘ g) :=
  ⟨(h.inj).comp (h'.inj), (h.surj).comp (h'.surj)⟩
theorem bij_iff_inv_functional : Bijective f ↔ (Relation.graph f).inv.Functional := by
  constructor
  · rintro ⟨h,h'⟩ b
    simp only [surj_iff] at h'
    obtain ⟨a,rfl⟩ := h' b
    exists a
    simp only [Relation.mem_inv_iff, Relation.mem_graph_iff, true_and]
    intro y h''
    symm
    apply h _ _ h''
  · intro h
    constructor
    · intro a a' h'
      obtain ⟨a₀, h₀⟩ := h (f a)
      simp only [Relation.mem_inv_iff, Relation.mem_graph_iff] at h₀
      rw[h'] at h₀
      rw[h₀.2 _ rfl]
      rw[h₀.2 _ h'.symm]
    · rw[surj_iff]
      intro b
      obtain ⟨a,h,_⟩ := h b
      simp only [Relation.mem_inv_iff, Relation.mem_graph_iff] at h
      exists a

noncomputable def Bijective.inv (h : Bijective f) (b : β) : α :=
  Exists.choose (h.surj.exists_preimage b)

/- inv -/
section
variable (h : Bijective f)
@[simp] theorem Bijective.inv_val_iff {a : α} {b : β}: h.inv b = a ↔ f a = b := by
  rw[Bijective.inv]
  have h' := Exists.choose_spec (h.surj.exists_preimage b)
  rw[← h.inj.eq_iff, Eq.comm]
  rw[← h']

@[simp] theorem Bijective.inv_val_val {a : α} : h.inv (f a) = a := by simp only [inv_val_iff]
@[simp] theorem Bijective.val_inv_val {b : β} : f (h.inv b) = b := by
  obtain ⟨a,rfl⟩ := h.surj.exists_preimage b
  simp only [inv_val_val]

@[simp] theorem comp_inv (h' : Bijective g) : (h.comp h').inv = h'.inv ∘ h.inv := by
  ext a
  simp only [comp_apply, Bijective.inv_val_iff, Bijective.val_inv_val]

@[simp] theorem Bijective.inv_bij : h.inv.Bijective := by
  constructor
  · intro b b' h'
    simp only [inv_val_iff, val_inv_val] at h'
    exact h'.symm
  · rw[surj_iff]
    intro b
    exists f b
    simp only [inv_val_val]

@[simp] theorem Bijective.inv_inv : h.inv_bij.inv = f := by
  ext a
  simp only [inv_val_iff, inv_val_val]

end

@[simp] theorem id_inv (h : Bijective id) : h.inv = (id : α → α) := by
  ext a
  simp only [id_eq, Bijective.inv_val_iff]

theorem Bijective.comp_inv (h : Bijective f) (h' : Bijective g) : (h.comp h').inv = h'.inv ∘ h.inv := by
  ext a
  simp only [comp_apply, inv_val_iff, val_inv_val]


@[simp] def IsRetractionOf (r : α → β) (g : β → α) := r ∘ g = id
@[simp] def IsSectionOf (s : α → β) (g : β → α) := g ∘ s = id
def HasRetraction (f : α → β) := ∃g : β → α, g.IsRetractionOf f
def HasSection (f : α → β) := ∃g : β → α, g.IsSectionOf f
@[simp] def IsInverseOf (f : α → β) (g : β → α) := IsRetractionOf f g ∧ IsSectionOf f g
def HasInverse f := ∃g : β → α, g.IsInverseOf f

section
variable {g g' : β → α} {f' : α → β}
theorem IsInverseOf.fg_eq (h : IsInverseOf f g) {b} : f (g b) = b := by
  rw[← @comp_apply _ _ _ f g, h.1]
  dsimp only [id_eq]
theorem IsInverseOf.gf_eq (h : IsInverseOf f g) {a} : g (f a) = a := by
  rw[← @comp_apply _ _ _ g f, h.2]
  dsimp only [id_eq]
theorem IsRetractionOf.fg_eq (h : IsRetractionOf f g) {b} : f (g b) = b := by
  rw[← @comp_apply _ _ _ f g, h]
  dsimp only [id_eq]
theorem IsSectionOf.gf_eq (h : IsSectionOf f g) {b} : g (f b) = b := by
  rw[← @comp_apply _ _ _ g f, h]
  dsimp only [id_eq]

theorem Surjective.hasSection (h : Surjective f) : HasSection f := by
  rw[surj_iff] at h
  obtain ⟨s, h⟩ := Classical.axiomOfChoice h
  exists s
  exact (funext h).symm

theorem Injective.hasRetraction [Nonempty α] (h : Injective f) : HasRetraction f := by
  classical
  let g (b : β) : α := by
    by_cases h' : ∃a, f a = b
    · exact Exists.choose h'
    · exact Classical.choice (by infer_instance)
  exists g
  ext a
  simp only [comp_apply, exists_apply_eq_apply, ↓reduceDIte, id_eq, g]
  have h' : f (@Exists.choose α (fun a_1 ↦ f a_1 = f a) ⟨_,rfl⟩) = f a := Exists.choose_spec (p := fun a_1 ↦ f a_1 = f a) ⟨_,rfl⟩
  apply h _ _ h'

theorem Surjective.comp_right_inj (h : f.Surjective) : (fun (x : β → γ) => (x ∘ f)).Injective := by
  intro g g' h'
  ext b
  obtain ⟨a, rfl⟩ := h.exists_preimage b
  simp only at h'
  rw[← comp_apply (f := g) (g := f), ← comp_apply (f := g')]
  rw[h']

theorem Surjective.comp_left_surj (h : f.Surjective) : (fun (x : γ → α) => (f ∘ x)).Surjective := by
  rw[surj_iff]
  intro g
  obtain ⟨a,h'⟩ : ∃ (a : γ → α), ∀ x, g x = f (a x) := by
    apply Classical.axiomOfChoice (r := fun x y => g x = f y)
    intro a
    obtain ⟨c, h⟩ := h.exists_preimage (g a)
    exists c
  exists a
  ext
  apply h'

theorem Injective.comp_right_surj [Nonempty α] (h : f.Injective) : (fun (x : β → γ) => (x ∘ f)).Surjective := by
  rw[surj_iff]
  intro b
  obtain ⟨r,h⟩ := h.hasRetraction
  exists b ∘ r
  rw[← comp_assoc, h, comp_id_right]


theorem Injective.comp_left_inj (h : f.Injective) : (fun (x : γ → α) => (f ∘ x)).Injective := by
  intro g g' h'
  ext c
  apply h _ _ (congrFun h' _)

theorem IsSectionOf.swap_retraction (h : IsSectionOf f g) : IsRetractionOf g f := h
theorem IsRetractionOf.swap_section (h : IsRetractionOf f g) : IsSectionOf g f := h

theorem IsSectionOf.inj (h : IsSectionOf f g) : Injective f := by
  intro a a' h'
  have h'' := congrArg g h'
  rw[h.gf_eq, h.gf_eq] at h''
  exact h''
theorem IsSectionOf.surj (h : IsSectionOf f g) : Surjective g := by
  rw[surj_iff]
  intro b
  exists f b
  exact h.gf_eq.symm
theorem IsRetractionOf.inj (h : IsRetractionOf f g) : Injective g :=
  h.swap_section.inj
theorem IsRetractionOf.surj (h : IsRetractionOf f g) : Surjective f :=
  h.swap_section.surj

theorem IsInverseOf.symm (h : IsInverseOf f g) : IsInverseOf g f := And.symm h
theorem IsInverseOf.bij' (h : IsInverseOf f g) : Bijective f :=
  ⟨h.2.inj, h.1.surj⟩
theorem IsInverseOf.bij (h : IsInverseOf f g) : Bijective g :=
  ⟨h.1.inj, h.2.surj⟩

theorem IsSectionOf.section_eq_iff_image_eq (h : f.IsSectionOf g) (h' : f'.IsSectionOf g)
    (h'' : Set.image f Set.univ = Set.image f' Set.univ) : f = f' := by
  ext a
  rw[Set.ext_iff] at h''
  have h'' := (h'' (f a)).mp (by simp)
  simp only [Set.mem_image_iff, Set.mem_univ, and_true] at h''
  obtain ⟨a', h''⟩ := h''
  have h''' := congrArg g h''
  rw[h.gf_eq, h'.gf_eq] at h'''
  rw[← h'''] at h''
  exact h''

theorem IsInverseOf.eq_inv (h : f.IsInverseOf g) : h.bij'.inv = g := by
  ext b
  simp only [Bijective.inv_val_iff]
  exact h.fg_eq

theorem IsInverseOf.eq_inv' (h : f.IsInverseOf g) : h.bij.inv = f := by
  ext a
  simp only [Bijective.inv_val_iff]
  exact h.gf_eq

theorem IsInverseOf.isInverse_eq (h : f.IsInverseOf g) (h' : f'.IsInverseOf g) : f = f' := by
  rw[← IsInverseOf.eq_inv' h, ← IsInverseOf.eq_inv' h']

theorem IsInverseOf.isInverse_eq' (h : f.IsInverseOf g) (h' : f.IsInverseOf g') : g = g' := by
  rw[← IsInverseOf.eq_inv h, ← IsInverseOf.eq_inv h']
end

section
variable {g : β → α} {f' : β → γ} {g' : γ → β}

theorem IsRetractionOf.comp (h : f.IsRetractionOf g) (h' : f'.IsRetractionOf g') :
    (f' ∘ f).IsRetractionOf (g ∘ g') := by
  unfold IsRetractionOf
  rw[← comp_assoc, comp_assoc (f := f)]
  rw[h]
  simp only [comp_id_left]
  exact h'

theorem IsSectionOf.comp (h : f.IsSectionOf g) (h' : f'.IsSectionOf g') :
    (f' ∘ f).IsSectionOf (g ∘ g') := by
  unfold IsSectionOf
  rw[← comp_assoc, comp_assoc (f := g')]
  rw[h']
  simp only [comp_id_left]
  exact h

theorem IsInverseOf.comp (h : f.IsInverseOf g) (h' : f'.IsInverseOf g') :
  (f' ∘ f).IsInverseOf (g ∘ g') := ⟨h.1.comp h'.1, h.2.comp h'.2⟩

theorem HasRetraction.comp (h : f.HasRetraction) (h' : f'.HasRetraction) :
  (f' ∘ f).HasRetraction := by
  obtain ⟨g, h⟩ := h
  obtain ⟨g', h'⟩ := h'
  exists g ∘ g'
  apply IsRetractionOf.comp h' h

theorem HasSection.comp (h : f.HasSection) (h' : f'.HasSection) :
  (f' ∘ f).HasSection := by
  obtain ⟨g, h⟩ := h
  obtain ⟨g', h'⟩ := h'
  exists g ∘ g'
  apply IsSectionOf.comp h' h

theorem HasInverse.comp (h : f.HasInverse) (h' : f'.HasInverse) :
  (f' ∘ f).HasInverse := by
  obtain ⟨g, h⟩ := h
  obtain ⟨g', h'⟩ := h'
  exists g ∘ g'
  apply IsInverseOf.comp h' h

theorem Bijective.inv_isInverseOf (h : f.Bijective) : h.inv.IsInverseOf f := by
  constructor
  · ext a
    simp only [comp_apply, inv_val_val, id_eq]
  · ext a
    simp only [comp_apply, val_inv_val, id_eq]


theorem hasInverse_iff_bij : f.HasInverse ↔ f.Bijective := by
  constructor
  · rintro ⟨g,h⟩
    exact h.bij
  · intro h
    exists h.inv
    apply Bijective.inv_isInverseOf


end
section
variable {f' : β → γ} {g : γ → α}

theorem isRetraction_of_comp (h : g.IsRetractionOf (f' ∘ f)) : (g ∘ f').IsRetractionOf f := h
theorem isSection_of_comp (h : g.IsSectionOf (f' ∘ f)) : (f ∘ g).IsSectionOf f' := h


theorem surj_of_inj_comp_surj (h : (f' ∘ f).Surjective) (h' : f'.Injective) : f.Surjective := by
  rw[surj_iff] at *
  intro b
  obtain ⟨a,h⟩ := h (f' b)
  specialize h' _ _ h
  exact ⟨a, h'⟩

theorem inj_of_surj_comp_inj (h : (f' ∘ f).Injective) (h' : f.Surjective) : f'.Injective := by
  intro b b' h''
  obtain ⟨a, rfl⟩ := h'.exists_preimage b
  obtain ⟨a', rfl⟩ := h'.exists_preimage b'
  rw[h _ _ h'']

theorem isRetraction_of_comp_surj (h : g.IsRetractionOf (f' ∘ f)) (h' : f.Surjective) :
    (f ∘ g).IsRetractionOf f' := by
  simp only [IsRetractionOf, comp_assoc] at *
  apply h'.comp_right_inj
  simp only [comp_id_left]
  rw[← comp_assoc, ← comp_assoc, comp_assoc (f := g), h, comp_id_right]

theorem isSection_of_comp_inj (h : g.IsSectionOf (f' ∘ f)) (h' : f'.Injective) :
    (g ∘ f').IsSectionOf f := by
  unfold IsSectionOf
  apply h'.comp_left_inj
  simp only [comp_id_right]
  rw[comp_assoc, comp_assoc, h, comp_id_left]

theorem bij_of_two_bij2 (h : (f ∘ g).Bijective) (h' : (g ∘ f').Bijective) : g.Bijective :=
  ⟨inj_of_comp_inj h.inj, surj_of_comp_surj h'.surj⟩

theorem bij_of_two_bij1 (h : (f ∘ g).Bijective) (h' : (g ∘ f').Bijective) : f.Bijective :=
  ⟨inj_of_surj_comp_inj h.inj (bij_of_two_bij2 h h').surj, surj_of_comp_surj h.surj⟩

theorem bij_of_two_bij3 (h : (f ∘ g).Bijective) (h' : (g ∘ f').Bijective) : f'.Bijective :=
  ⟨inj_of_comp_inj h'.inj, surj_of_inj_comp_surj h'.surj (bij_of_two_bij2 h h').inj⟩

theorem bij_of_surj_surj_inj1 {f' : β → γ} (h : (f' ∘ f ∘ g).Surjective) (h' : (f ∘ g ∘ f').Surjective)
    (h'' : (g ∘ f' ∘ f).Injective) : f'.Bijective :=
  ⟨inj_of_comp_inj (g := f') (f := g) $ inj_of_surj_comp_inj h'' $ surj_of_comp_surj h',
   surj_of_comp_surj h⟩

theorem bij_of_surj_surj_inj2 {f' : β → γ} (h : (f' ∘ f ∘ g).Surjective) (h' : (f ∘ g ∘ f').Surjective)
    (h'' : (g ∘ f' ∘ f).Injective) : f.Bijective :=
  ⟨inj_of_comp_inj (comp_assoc ▸ h''),
   surj_of_comp_surj h'⟩

theorem bij_of_surj_inj3 {f' : β → γ} (h : (f' ∘ f ∘ g).Surjective)
    (h'' : (g ∘ f' ∘ f).Injective) : g.Bijective :=
  ⟨inj_of_surj_comp_inj (comp_assoc ▸ h'') $ surj_of_comp_surj (comp_assoc ▸ h),
  surj_of_inj_comp_surj (comp_assoc ▸ h) $ inj_of_comp_inj h''⟩

end
section
theorem Surjective.factor_after {g : α → γ} (h : f.Surjective) (h' : ∀ a a', f a = f a' → g a = g a') :
    ∃! p, g = p ∘ f := by
  obtain ⟨s, h⟩ := h.hasSection
  exists g ∘ s
  constructor
  · dsimp only
    ext a
    apply h'
    simp only [comp_apply, h.gf_eq]
  · rintro p' rfl
    ext a
    simp only [comp_apply, h.gf_eq]

theorem Injective.factor_before {g : γ → β} (h : f.Injective) (h' : g '' Set.univ ⊆ f '' Set.univ) :
    ∃! i, g = f ∘ i := by
  by_cases h'' : Nonempty α
  · obtain ⟨r, h⟩ := h.hasRetraction
    exists r ∘ g
    constructor
    · dsimp only
      ext a
      simp only [comp_apply, h.fg_eq]
      specialize h' (a := g a)  (by simp only [Set.val_mem_image_univ])
      rw[Set.mem_image_iff] at h'
      obtain ⟨a',h', _⟩ := h'
      rw[h']
      rw[h.fg_eq]
    · rintro r' rfl
      ext
      simp only [comp_apply, h.fg_eq]
  · have h''' : f '' Set.univ = ∅ := by
      ext x
      simp only [Set.mem_image_iff, Set.mem_univ, and_true, Set.not_mem_empty, iff_false,
        not_exists]
      intro a
      exfalso
      exact h'' ⟨a⟩
    simp only [h''', Set.subset_empty_iff, image_empty_iff_empty] at h'
    have j : γ → Empty := by
      intro c
      have h := @Set.mem_univ _ c
      rw[h'] at h
      exfalso
      exact h
    exists fun a => (j a).elim
    constructor
    · apply (func_subsingleton_iff_to_empty j).allEq
    · intro _ _
      apply (func_subsingleton_iff_to_empty j).allEq
end

@[simp] theorem into_unit_surjective [Nonempty α] {f : α → Unit} : f.Surjective := by
  rw[surj_iff]
  rintro ⟨⟩
  exists Classical.choice (by infer_instance)

@[simp] theorem out_of_unit_injective {f : Unit → α} : f.Injective := by
  rintro ⟨⟩ ⟨⟩ _
  rfl

theorem curry_bijective : (curry : (α × β → γ) → α → β → γ).Bijective := by
  apply hasInverse_iff_bij.1
  exists uncurry

theorem uncurry_bijective : (uncurry : (α → β → γ) → (α × β → γ)).Bijective := by
  apply hasInverse_iff_bij.1
  exists curry

theorem curry_uncurry_inverse : (curry : (α × β → γ) → α → β → γ).IsInverseOf uncurry := by
  constructor <;> (ext; simp)

def Injection (α β : Type*) := {f : α → β // f.Injective}
def Bijection (α β : Type*) := {f : α → β // f.Bijective}
instance {α β} : CoeFun (Bijection α β) (fun _ => α → β) where
  coe f := f.1
instance {α β} : CoeFun (Injection α β) (fun _ => α → β) where
  coe f := f.1
noncomputable def Bijection.invfun (f : Bijection α β) := f.2.inv
noncomputable def Bijection.inv (f : Bijection α β) : Bijection β α := ⟨f.2.inv, f.2.inv_bij⟩
@[simp] theorem Bijection.val_inv_val (f : Bijection α β) {b} : f (f.inv b) = b := by
  simp only [inv, Bijective.val_inv_val]
@[simp] theorem Bijection.inv_val_val (f : Bijection α β) {a} : f.inv (f a) = a := by
  simp only [inv, Bijective.inv_val_val]
@[simp] def bijection_of_funcs (f : α → β) (g : β → α) (h : ∀ b, f (g b) = b) (h' : ∀ a, g (f a) = a) : Bijection α β :=
  ⟨f, IsInverseOf.bij ⟨funext h', funext h⟩⟩
end Function

theorem Subtype.coe.inj {p : α → Prop}: Function.Injective (fun ⟨x, _⟩ => x : { x // p x } → α) := by
  rintro ⟨a,_⟩ ⟨a',_⟩ h
  simp only [mk.injEq] at *
  exact h
theorem Eq.rec_of_inj {ι' : Type*} {ι : Type*} {x : ι → Type*}   {i i' : ι'} (f : ι' → ι) (h : f i = f i') (h' : f.Injective) (a : (i : ι') → x (f i)) : Eq.rec (a i) h = a i' := by
  replace h := h' _ _ h
  cases h
  simp only
