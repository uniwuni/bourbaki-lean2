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

instance totally_ordered_finiteCharacter [PartialOrder α] :
    FiniteCharacter {s : Set α | ∀ x y : s, Comparable x y} where
  mem_iff_finite_subset_mem {x} := by
    constructor
    · intro comp y sub fin ⟨a,h⟩ ⟨b,h'⟩
      simp only [Comparable, Subtype.le_iff_val]
      have := comp ⟨a,sub h⟩ ⟨b, sub h'⟩
      simp only [Comparable, Subtype.le_iff_val] at this
      exact this
    · intro fincomp ⟨a,h⟩ ⟨b,h'⟩
      have : Finite ({a,b} : Set α) := by infer_instance
      specialize fincomp _ _ this ⟨a,Or.inl rfl⟩ ⟨b, Or.inr rfl⟩
      · rintro _ (rfl|rfl) <;> assumption
      · exact fincomp

instance FiniteCharacter.inductiveOrder [FiniteCharacter s] (ne : s.Nonempty) : InductiveOrder s := by
  apply subset_chain_iUnion_inductive ne
  intro t ne sub chain
  rw[mem_iff_finite_subset_mem]
  intro Y Ysub Yfin
  by_cases ne' : Y.Nonempty
  · have this : ∀ y : Y, ∃ z, z ∈ t ∧ y.val ∈ z := by
      intro ⟨y,memy⟩
      obtain ⟨⟨i,imem⟩,hi⟩ := Ysub memy
      exists i
    obtain ⟨f,hf⟩ := Classical.axiomOfChoice this
    let Z := f '' Set.univ
    have : Finite Z := Finite.image _
    have Zsubt : Z ⊆ t := by
      intro x hx
      rw[Set.mem_image_iff] at hx
      obtain ⟨x,rfl,_⟩ := hx
      apply (hf x).1
    obtain ⟨Ymem,hYmem⟩ := ne'
    have : Nonempty Z := ⟨f ⟨Ymem, hYmem⟩, Set.val_mem_image_of_mem trivial⟩
    let _inst : TotalOrder Z := by
      constructor
      intro ⟨x,memx⟩ ⟨y,memy⟩
      rw[Set.mem_image_iff] at memx memy
      obtain ⟨x,rfl,_⟩ := memx
      obtain ⟨y,rfl,_⟩ := memy
      have tx := (hf x).1
      have ty := (hf y).1
      exact chain _ tx _ ty
    obtain ⟨g,greatest⟩ := TotalOrder.finite_greatest (α := Z)
    have bwah (y : Y) : y.val ∈ (g : Set α) := by
      have : f y ∈ Z := Set.val_mem_image_of_mem trivial
      have := greatest ⟨_,this⟩
      simp only [Subtype.le_iff_val, le_set_iff_subset] at this
      apply this
      exact (hf _).2
    have : Y ⊆ (g : Set α) := fun x hx => bwah ⟨x,hx⟩
    apply (mem_iff_finite_subset_mem (x := g.val)).mp
    · apply sub
      apply Zsubt
      exact g.property
    · assumption
    · assumption
  · obtain ⟨memt, ht⟩ := ne
    have hs := sub ht
    rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at ne'
    rw[ne']
    rw[mem_iff_finite_subset_mem] at hs
    specialize hs ∅ Set.empty_subset
    apply hs inferInstance

theorem FiniteCharacter.has_maximal (h : FiniteCharacter s) (ne : s.Nonempty) : ∃ x : s, Maximal x :=
  (FiniteCharacter.inductiveOrder ne).has_maximal
