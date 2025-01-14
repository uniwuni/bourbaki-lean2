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

theorem IsPartition.image_bij (h : IsPartition x) (h' : f.Bijective) : IsPartition (Set.image f ∘ x) := by
  constructor
  · simp only [IsCovering, Function.comp_apply]
    rw[← Set.iUnion_image, h.1, h'.surj]
  · simp only [Disjoint, ne_eq, Function.comp_apply]
    intro i i' ne
    ext a
    simp
    rintro a rfl mem b eq mem'
    have eq' := h.2 i i' ne
    obtain rfl := h'.inj _ _ eq
    have : a ∈ x i ∩ x i' := ⟨mem,mem'⟩
    rwa[eq'] at this


theorem IsPartition.inj_of_nonempty (h : IsPartition x) (h' : ∀ i, (x i).Nonempty) : x.Injective :=
  h.2.inj_of_nonempty h'

theorem IsPartition.subset_of_finerThan (h : IsPartition x) (h' : IsPartition x') (hne : ∀ i, (x i).Nonempty) (hne' : ∀ i', (x' i').Nonempty)  (h'' : FinerThan x x')
    (i' : ι') : ∃ i, x i ⊆ x' i' := by
  obtain ⟨a, hmem⟩ := hne' i'
  obtain ⟨i, hi⟩ := isPartition_iff.mp h a
  exists i
  obtain ⟨i'2, hi'2⟩ := h'' i
  have := Disjoint.eq_of_subset_elem h'.2 (hne i) hmem hi.1 hi'2
  rwa[this]


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

structure Partition (α : Type*) where
  subsets : Set (Set α)
  isPartition' : IsPartition (fun (x : subsets) => x.val)
  empty_not_included : ∅ ∉ subsets

theorem Partition.eq_iff {p q : Partition α} : p = q ↔ p.subsets = q.subsets := by
  constructor
  · intro h
    rw[h]
  · intro h
    rcases p
    rcases q
    simp only [mk.injEq]
    exact h

@[ext] theorem Partition.eq_of {p q : Partition α} : p.subsets = q.subsets → p = q := Partition.eq_iff.mpr

def Partition.partition (p : Partition α) : p.subsets → Set α := Subtype.val

@[simp] theorem Partition.isPartition (p : Partition α) : IsPartition p.partition := p.isPartition'

@[simp] theorem partition.val_partition {p : Partition α} {q} {h : q ∈ p.subsets}: p.partition ⟨q,h⟩ = q := rfl


theorem IsPartition.equivalent_partition (h : IsPartition x) (ne : (i : _) → (x i).Nonempty) : ∃ p : Partition α, FinerThan p.partition x ∧ FinerThan x p.partition := by
  let q := Set.image x Set.univ
  have h2 : IsPartition (fun (x : q) => x.val) := by
    constructor
    · apply isCovering_of_mem_exists
      intro a
      have ⟨i,h'⟩ := h.1.mem_exists a
      exists ⟨x i, ⟨i, by simp only [Relation.mem_graph_iff, mem_univ, and_self]⟩⟩
    · intro ⟨y, ⟨i,hy, _⟩⟩ ⟨z,⟨j,hz,_⟩⟩ ne'
      ext a
      simp only [ne_eq, Subtype.eq_iff, mem_inter_iff, not_mem_empty, iff_false, not_and] at *
      rw[Relation.mem_graph_iff] at hy hz
      intro h' h''
      rcases hy
      rcases hz
      have := h.2 i j (fun h => ne' $ congrArg x h)
      have that : a ∈ x i ∩ x j := ⟨h',h''⟩
      rwa[this] at that
  have h3 : ∅ ∉ q := by
    rintro ⟨i, ⟨r,_⟩⟩
    simp only [Relation.mem_graph_iff] at r
    specialize ne i
    rw[← r] at ne
    apply empty_not_nonempty ne
  exists ⟨q,h2,h3⟩
  constructor
  · intro ⟨a, ⟨i, ⟨h, _⟩⟩⟩
    simp only [Relation.mem_graph_iff] at h
    obtain rfl := h
    exists i
  · intro i
    exists ⟨x i, ⟨i, by simp only [Relation.mem_graph_iff, mem_univ, and_self]⟩⟩

theorem Partition.all_nonempty (p : Partition α) {a} (h' : a ∈ p.subsets) : a.Nonempty := by
  rw[nonempty_iff_neq_empty]
  rintro rfl
  apply p.empty_not_included h'

end Set
