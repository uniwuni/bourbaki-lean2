import BourbakiLean2.Set.Operations
variable {α β : Type*} {ι ι' ι'' : Type*} {a : α} {i : ι} {x : ι → Set α} {x' : ι' → Set α} {x'' : ι'' → Set α} {f f' : α → β} {y : ι → Set β}

namespace Set
@[simp] def IsCovering (x : ι → Set α) := ⋃ i, x i = Set.univ
@[simp] def FinerThan (x : ι → Set α) (x' : ι' → Set α) := ∀ i, ∃ i', x i ⊆ x' i'

theorem IsCovering.mem_exists (h : IsCovering x) (a : _) : ∃i, a ∈ x i := by
  rw[← mem_iUnion_iff, h]
  exact mem_univ

theorem isCovering_of_mem_exists (h : ∀ a, ∃ i, a ∈ x i) : IsCovering x := by
  ext a
  simp only [mem_iUnion_iff, h, mem_univ]

theorem isCovering_iff_mem_exists : IsCovering x ↔ ∀ a, ∃ i, a ∈ x i :=
  ⟨fun h _ => h.mem_exists _, isCovering_of_mem_exists⟩

theorem univ_isCovering [Nonempty ι] : IsCovering (Function.const ι (univ : Set α)) := by
  ext a
  simp only [Function.const_apply, mem_iUnion_iff, mem_univ, exists_const]

@[refl] theorem finerThan_refl : FinerThan x x := fun i => ⟨i,subset_refl _⟩
@[trans] theorem finerThan_trans (h : FinerThan x x') (h' : FinerThan x' x'') : FinerThan x x'' := by
  intro i
  replace ⟨i', h⟩ := h i
  replace ⟨i'', h'⟩ := h' i'
  exists i''
  exact subset_trans h h'

theorem comp_finerThan {f : ι' → ι} : FinerThan (x ∘ f) x := by
  intro i
  exists f i

theorem IsCovering.isCovering_of_supset {x' : ι → Set α} (h : IsCovering x) (h' : ∀ i, x i ⊆ x' i) :
    IsCovering x' := by
  replace h' := iUnion_mono h'
  dsimp only [IsCovering]
  rw[← univ_subset_iff]
  trans
  · rw[← h]
  · exact h'

theorem IsCovering.inter_isCovering (h : IsCovering x) (h' : IsCovering x') :
    IsCovering (fun (i,i') => x i ∩ x' i') := by
  ext a
  simp only [mem_iUnion_iff, mem_inter_iff, Prod.exists, exists_and_left, exists_and_right,
    mem_univ, iff_true]
  exact ⟨h.mem_exists _, h'.mem_exists _⟩

@[simp] theorem inter_finerThan_left : FinerThan (fun (i,i') => x i ∩ x' i') x := by
  simp only [FinerThan, Prod.forall]
  intro i i'
  exists i
  simp only [inter_subset_left]

@[simp] theorem inter_finerThan_right : FinerThan (fun (i,i') => x i ∩ x' i') x' := by
  simp only [FinerThan, Prod.forall]
  intro i i'
  exists i'
  simp only [inter_subset_right]

@[simp] theorem finerThan_inter_iff : FinerThan x (fun (i,i') => x' i ∩ x'' i') ↔ (FinerThan x x' ∧ FinerThan x x'') := by
  constructor
  · intro h
    exact ⟨finerThan_trans h inter_finerThan_left, finerThan_trans h inter_finerThan_right⟩
  · rintro ⟨h, h'⟩
    intro i
    replace ⟨i',h⟩ := h i
    replace ⟨i'',h'⟩ := h' i
    exists ⟨i',i''⟩
    rw[subset_inter_iff]
    exact ⟨h,h'⟩

theorem IsCovering.image_isCovering_of_surj (h : IsCovering x) (h' : f.Surjective) : IsCovering (Set.image f ∘ x) := by
  simp only [IsCovering, Function.comp_apply]
  rw[← iUnion_image, h, h']

theorem IsCovering.preimage (h : IsCovering y) : IsCovering (Set.preimage f ∘ y) := by
  simp only [IsCovering, Function.comp_apply]
  rw[← iUnion_preimage, h, Function.preimage_univ]

theorem IsCovering.functions_eq_of_all_eq (h : IsCovering x) (h' : ∀ i, ∀ a ∈ x i, f a = f' a) : f = f' := by
  funext a
  replace ⟨i,h⟩ := h.mem_exists a
  apply h' _ _ h

noncomputable def IsCovering.glue {β : α → Type*} (h : IsCovering x) (f : (i : ι) → (a : x i) → β a) : (a : α) → β a := by
  intro a
  let i := Classical.choose (h.mem_exists a)
  replace h := Classical.choose_spec (h.mem_exists a)
  exact f i ⟨_,h⟩

@[simp] theorem IsCovering.glue_agrees {β : α → Type*} (h : IsCovering x) {f : (i : ι) → (a : x i) → β a}
  (h' : ∀ (a i j) (h : a ∈ x i) (h' : a ∈ x j), f i ⟨a, h⟩ = f j ⟨a,h'⟩) (h'' : a ∈ x i)
    : h.glue f a = f i ⟨a, h''⟩ := by
  simp only [glue]
  have h''' := Classical.choose_spec (h.mem_exists a)
  apply h'

theorem IsCovering.glue_unique (h : IsCovering x) {f : (i : ι) → x i → β} {g : α → β}
  (h' : ∀ (a i j) (h : a ∈ x i) (h' : a ∈ x j), f i ⟨a, h⟩ = f j ⟨a,h'⟩)
  (h'' : ∀ (a i) (h : a ∈ x i), g a = f i ⟨a, h⟩)
    : h.glue f = g := by
  apply h.functions_eq_of_all_eq
  intro i a h'''
  rw[h.glue_agrees h' h''']
  rw[h'' _ _ h''']

end Set
