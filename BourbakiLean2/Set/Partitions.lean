import BourbakiLean2.Set.Coverings
variable {α β : Type*} {ι ι' ι'' : Type*} {a : α} {i j : ι} {x : ι → Set α} {x' : ι' → Set α} {x'' : ι'' → Set α} {f f' : α → β} {y : ι → Set β}
namespace Set
def IsPartition (x : ι → Set α) := IsCovering x ∧ Disjoint x

theorem eq_of_mem_disjoint (h : Disjoint x) (h' : a ∈ x i) (h'' : a ∈ x j) : i = j := by
  by_contra h'''
  specialize h i j h'''
  replace h' : a ∈ x i ∩ x j := ⟨h',h''⟩
  rw[h] at h'
  exact h'

theorem IsPartition.eq_of_mem (h : IsPartition x) (h' : a ∈ x i) (h'' : a ∈ x j) : i = j := by
  apply eq_of_mem_disjoint h.2 h' h''

theorem isPartition_iff : IsPartition x ↔ ∀ a, ∃! i, a ∈ x i := by
  constructor
  · intro h a
    have ⟨i, h'⟩ := h.1.mem_exists a
    exists i
    constructor
    · apply h'
    · intro j h''
      apply h.eq_of_mem h'' h'
  · intro h
    constructor
    · rw[isCovering_iff_mem_exists]
      intro a
      replace ⟨i,h,_⟩ := h a
      exact ⟨i,h⟩
    · intro i j h'
      ext a
      simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
      intro h'' h'''
      obtain ⟨_,_,h⟩ := h a
      rw[h _ h'',h _ h'''] at h'
      exact h' rfl

theorem IsPartition.preimage (h : IsPartition y) : IsPartition (Set.preimage f ∘ y) := by
  constructor
  · exact h.1.preimage
  · exact h.2.preimage

theorem IsPartition.inj_of_nonempty (h : IsPartition x) (h' : ∀ i, (x i).Nonempty) : x.Injective :=
  h.2.inj_of_nonempty h'

@[simp] theorem IsPartition.glue_agrees {β : α → Type*} (h : IsPartition x) {f : (i : ι) → (a : x i) → β a} (h' : a ∈ x i) :
    h.1.glue f a = f i ⟨a, h'⟩ := by
  apply h.1.glue_agrees
  intro a i j h'' h'''
  obtain rfl : i = j := h.eq_of_mem h'' h'''
  simp only

theorem singleton_partition : IsPartition (fun x : α => {x}) := by
  constructor
  · ext a
    simp only [mem_iUnion_iff, mem_singleton_iff, exists_eq', mem_univ]
  · intro i j h
    ext a
    simp only [mem_inter_iff, mem_singleton_iff, not_mem_empty, iff_false, not_and]
    intro h'
    rw[h']
    exact h

end Set
