import BourbakiLean2.Data.Finite

variable {α : Type*}
instance [h : Finite α] : Finite (Op α) := h
instance [h : Nonempty α] : Nonempty (Op α) := h
theorem RightDirected.finite_bounded_above [Preorder α] [RightDirected α] : ∀ {a : Set α}
    [Finite a] (_ : a.Nonempty), a.BoundedAbove := by
  refine fun {a} => Finite.set_induction (p := fun a => a.Nonempty → a.BoundedAbove) ?h1 ?h2 a
  · simp only [Set.empty_not_nonempty, false_implies]
  · intro x a fin nmem bd _
    by_cases isne : a.Nonempty
    · obtain ⟨ub,isub⟩ := bd isne
      exists RightDirected.ub ub x
      rintro b (hb|rfl)
      · apply le_trans (isub _ hb) RightDirected.le_ub_left
      · apply RightDirected.le_ub_right
    · rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at isne
      rw[isne]
      simp only [Set.empty_union]
      exists x
      rintro _ rfl
      rfl

theorem LeftDirected.finite_bounded_above [Preorder α] [h : LeftDirected α] : ∀ {a : Set α}
    [Finite a] (_ : a.Nonempty), a.BoundedBelow := by
  refine fun {a} => Finite.set_induction (p := fun a => a.Nonempty → a.BoundedBelow) ?h1 ?h2 a
  · simp only [Set.empty_not_nonempty, false_implies]
  · intro x a fin nmem bd _
    by_cases isne : a.Nonempty
    · obtain ⟨ub,isub⟩ := bd isne
      exists LeftDirected.lb ub x
      rintro b (hb|rfl)
      · apply le_trans LeftDirected.lb_le_left (isub _ hb)
      · apply LeftDirected.lb_le_right
    · rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at isne
      rw[isne]
      simp only [Set.empty_union]
      exists x
      rintro _ rfl
      rfl

theorem SupSemilattice.finite_hasLUB [SupSemilattice α] : ∀ {a : Set α}
    [Finite a] (_ : a.Nonempty), ∃ x, IsLUB a x := by
  refine fun {a} => Finite.set_induction (p := fun a => a.Nonempty → ∃ x, IsLUB a x) ?h1 ?h2 a
  · simp only [Set.empty_not_nonempty, false_implies]
  · intro x a fin nmem bd _
    by_cases isne : a.Nonempty
    · obtain ⟨ub,isub⟩ := bd isne
      exists ub ⊔ x
      rw[isLUB_iff]
      constructor
      . rintro b (hb|rfl)
        · apply le_trans (isub.1 _ hb) le_sup_left
        · exact le_sup_right
      · intro b isub2
        rw[sup_le_iff]
        constructor
        · rw[isub.le_iff]
          intro x hx
          apply isub2 _ $ Or.inl hx
        · apply isub2 _ $ Or.inr rfl
    · rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at isne
      rw[isne]
      simp only [Set.empty_union]
      exists x
      simp only [isLUB_singleton_iff_eq]

theorem SupSemilattice.finite_hasLUB' [SupSemilattice α] [HasLeast α]: ∀ {a : Set α}
    [Finite a], ∃ x, IsLUB a x := by
  intro a fin
  by_cases h : a.Nonempty
  · apply SupSemilattice.finite_hasLUB h
  · rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at h
    rw[h]
    exists ⊥
    simp only [isLUB_empty_iff_least, Least, least_le, implies_true]

theorem InfSemilattice.finite_hasGLB [InfSemilattice α] : ∀ {a : Set α}
    [Finite a] (_ : a.Nonempty), ∃ x, IsGLB a x := by
  refine fun {a} => Finite.set_induction (p := fun a => a.Nonempty → ∃ x, IsGLB a x) ?h1 ?h2 a
  · simp only [Set.empty_not_nonempty, false_implies]
  · intro x a fin nmem bd _
    by_cases isne : a.Nonempty
    · obtain ⟨ub,isub⟩ := bd isne
      exists ub ⊓ x
      rw[isGLB_iff]
      constructor
      . rintro b (hb|rfl)
        · apply le_trans inf_le_left (isub.1 _ hb)
        · exact inf_le_right
      · intro b isub2
        rw[le_inf_iff]
        constructor
        · rw[isub.ge_iff]
          intro x hx
          apply isub2 _ $ Or.inl hx
        · apply isub2 _ $ Or.inr rfl
    · rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at isne
      rw[isne]
      simp only [Set.empty_union]
      exists x
      simp only [isGLB_singleton_iff_eq]

theorem InfSemilattice.finite_hasGLB' [InfSemilattice α] [HasGreatest α]: ∀ {a : Set α}
    [Finite a], ∃ x, IsGLB a x := by
  intro a fin
  by_cases h : a.Nonempty
  · apply InfSemilattice.finite_hasGLB h
  · rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at h
    rw[h]
    exists ⊤
    simp only [isGLB_empty_iff_greatest, Greatest, le_greatest, implies_true]


theorem TotalOrder.finite_has_greatest [TotalOrder α] : ∀ {a : Set α}
    [_hf : Finite a] (_ : a.Nonempty), ∃ x : a, Greatest x := by
  refine fun {a} => Finite.set_induction (p := fun a => a.Nonempty → ∃ x : a, Greatest x) ?h1 ?h2 a
  · simp only [Set.empty_not_nonempty, Greatest, Subtype.le_iff_val, Subtype.forall,
    Set.not_mem_empty, false_implies, implies_true, Subtype.exists, exists_prop, and_true,
    exists_false, imp_self]
  · intro x a fin nmem bd _
    by_cases isne : a.Nonempty
    · obtain ⟨⟨ub,mem⟩,isub⟩ := bd isne
      exists ⟨max ub x, by rcases max_eq_either ub x with (eq|eq)
                           · rw[eq]; left; assumption
                           · rw[eq]; right; rfl ⟩
      rintro ⟨y,(h|rfl)⟩
      · have := isub ⟨y,h⟩
        simp only [Subtype.le_iff_val, ge_iff_le] at this |-
        apply le_trans this le_sup_left
      · simp only [Subtype.le_iff_val, le_sup_right]
    · rw[Set.nonempty_iff_neq_empty, Ne, Classical.not_not] at isne
      rw[isne]
      exists ⟨x,Or.inr rfl⟩
      simp only [Greatest, Subtype.le_iff_val, Subtype.forall, Set.empty_union,
        Set.mem_singleton_iff, forall_eq, le_rfl]

theorem TotalOrder.finite_has_least [TotalOrder α] {a : Set α}
    [hf : Finite a] (hne : a.Nonempty) : ∃ x : a, Least x := by
  obtain ⟨x,hx⟩ := finite_has_greatest (α := Op α) (a := a) (_hf := hf) hne
  exists x

theorem TotalOrder.finite_greatest [ne : Nonempty α] [TotalOrder α] [Finite α]: ∃ x : α, Greatest x := by
  obtain ⟨ne⟩ := ne
  obtain ⟨⟨x,mem⟩,le⟩ := finite_has_greatest (a := Set.univ) ⟨ne,trivial⟩
  exists x
  intro y
  apply le ⟨y,trivial⟩

theorem TotalOrder.finite_least [ne : Nonempty α] [TotalOrder α] [Finite α]: ∃ x : α, Least x := by
  obtain ⟨ne⟩ := ne
  obtain ⟨⟨x,mem⟩,le⟩ := finite_has_least (a := Set.univ) ⟨ne,trivial⟩
  exists x
  intro y
  apply le ⟨y,trivial⟩

instance [TotalOrder α] [Finite α] : WellOrder α where
  existsLeast := by
    intro s ne
    obtain ⟨⟨x,a⟩,h⟩ := TotalOrder.finite_has_least ne
    exact ⟨x,a,h⟩

instance partialOrder_finite_inductive [PartialOrder α] [Finite α] [hne : Nonempty α] : InductiveOrder α where
  chain_boundedAbove := by
    intro s cmp
    let wah : TotalOrder s := by
      constructor
      intro ⟨x,h⟩ ⟨y,h'⟩
      apply cmp _ h _ h'
    by_cases ne : Nonempty s
    · obtain ⟨x,g⟩ := wah.finite_greatest (α := s)
      exists x
      intro a h
      have := g ⟨a,h⟩
      exact this
    · have : s = ∅ := by
        by_contra h'
        rw[← Ne, ← Set.nonempty_iff_neq_empty] at h'
        obtain ⟨a,m⟩ := h'
        exact (ne ⟨a,m⟩).elim
      rw[this]
      obtain ⟨a⟩ := hne
      exists a
      simp only [UpperBound.empty]

theorem PartialOrder.finite_has_maximal [PartialOrder α] [Finite α] [Nonempty α] :
    ∃ x : α, Maximal x := InductiveOrder.has_maximal

theorem PartialOrder.finite_has_minimal [PartialOrder α] [Finite α] [Nonempty α] :
    ∃ x : α, Minimal x := by
  conv => arg 1; intro x; rw[← maximal_toOp_iff_minimal]
  apply InductiveOrder.has_maximal (α := Op α)
