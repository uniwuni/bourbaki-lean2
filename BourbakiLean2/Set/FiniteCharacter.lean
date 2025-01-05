import BourbakiLean2.Order.Finite

variable {α ι : Type*} {s t : Set (Set α)}

class FiniteCharacter (s : Set (Set α)) where
  mem_iff_finite_subset_mem {x : Set α} : x ∈ s ↔ (∀ y, y ⊆ x → Finite y → y ∈ s)

theorem mem_iff_finite_subset_mem [FiniteCharacter s] {x : Set α} : x ∈ s ↔ (∀ y, y ⊆ x → Finite y → y ∈ s) :=
  FiniteCharacter.mem_iff_finite_subset_mem

instance: FiniteCharacter (∅ : Set (Set α)) where
  mem_iff_finite_subset_mem {x} := by
    simp only [Set.not_mem_empty, Finite.iff, imp_false, false_iff, Classical.not_forall, not_imp,
      Classical.not_not]
    exists ∅
    simp only [Set.empty_subset, exists_const]
    infer_instance

instance: FiniteCharacter (Set.univ : Set (Set α)) where
  mem_iff_finite_subset_mem {x} := by
    simp only [Set.mem_univ, Finite.iff, implies_true]

instance [FiniteCharacter s] [FiniteCharacter t] : FiniteCharacter (s ∩ t) where
  mem_iff_finite_subset_mem {x} := by
    have h := mem_iff_finite_subset_mem (s := s) (x := x)
    have h' := mem_iff_finite_subset_mem (s := t) (x := x)
    simp only [Set.mem_inter_iff]
    rw[h, h']
    constructor
    · intro ⟨h,h'⟩ y hy hf
      exact ⟨h y hy hf, h' y hy hf⟩
    · intro h
      constructor
      · exact fun y hy hf => (h y hy hf).1
      · exact fun y hy hf => (h y hy hf).2

instance {s : ι → Set (Set α)} [∀ i, FiniteCharacter $ s i]  : FiniteCharacter (⋂ i, s i) where
  mem_iff_finite_subset_mem {x} := by
    have h i := mem_iff_finite_subset_mem (s := s i) (x := x)
    simp only [Set.mem_iInter_iff]
    conv => lhs; intro i; rw[h]
    constructor
    · exact fun h y hy hf i => h i y hy hf
    · exact fun h i y hy hf => h y hy hf i
