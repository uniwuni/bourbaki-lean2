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

@[simp] theorem subset_preimage_image {x : Set α} : x ⊆ f ⁻¹' (f '' x) := by
  intro a h
  simp only [Set.mem_preimage_iff, Set.mem_image_iff]
  exists a

@[simp] theorem image_preimage_subset {y : Set β} : f '' (f ⁻¹' y) ⊆ y := by
  intro a h
  simp only [Set.mem_image_iff, Set.mem_preimage_iff] at h
  obtain ⟨_,rfl,h⟩ := h
  exact h

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


@[simp] theorem Bijective.inv_val_iff (h : Bijective f) {a : α} {b : β}: h.inv b = a ↔ f a = b := by
  rw[Bijective.inv]
  have h' := Exists.choose_spec (h.surj.exists_preimage b)
  rw[← h.inj.eq_iff, Eq.comm]
  rw[← h']

@[simp] theorem Bijective.inv_val_val (h : Bijective f) {a : α} : h.inv (f a) = a := by simp only [inv_val_iff]
@[simp] theorem Bijective.val_inv_val (h : Bijective f) {b : β} : f (h.inv b) = b := by
  obtain ⟨a,rfl⟩ := h.surj.exists_preimage b
  simp only [inv_val_val]

end Function

theorem Subtype.coe.inj {p : α → Prop}: Function.Injective (fun ⟨x, _⟩ => x : { x // p x } → α) := by
  rintro ⟨a,_⟩ ⟨a',_⟩ h
  simp only [mk.injEq] at *
  exact h
