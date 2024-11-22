import BourbakiLean2.Set.Rel
import BourbakiLean2.Set.Operations
import BourbakiLean2.Function.Basic
variable {α β : Type*}
/-
theorem Relation.graph_of_bij_iff {r : Relation α β} {s : Relation β α} :
    (∃ f g, r = graph f ∧ s = graph g ∧ f.IsInverseOf g) ↔
      ((∀ a, s.image (r.image {a}) = {a}) ∧ (∀ b, r.image (s.image {b}) = {b})) := by
  constructor
  · rintro ⟨f,⟨g,rfl,rfl,h⟩⟩
    constructor
    · intro a
      rw[← Set.image, ← Set.image]
      simp only [Function.image_singleton, h.gf_eq]
    · intro b
      rw[← Set.image, ← Set.image]
      simp only [Function.image_singleton, h.fg_eq]
  · intro ⟨h, h'⟩
    have hsr
    have h1 : ∀ a, (r.image {a}).Nonempty := by
      intro a
      apply Classical.byContradiction
      intro h''
      rw[Set.nonempty_iff_neq_empty] at h''
      simp only [ne_eq, Classical.not_not] at h''
      specialize h a
      rw[h'', image_empty] at h
      exact Set.singleton_neq_empty h.symm
    have h2 : ∀ a, (s.image {a}).Nonempty := by
      intro a
      apply Classical.byContradiction
      intro h''
      rw[Set.nonempty_iff_neq_empty] at h''
      simp only [ne_eq, Classical.not_not] at h''
      specialize h' a
      rw[h'', image_empty] at h'
      exact Set.singleton_neq_empty h'.symm
    exists fun a => Classical.choose (h1 a)
    exists fun a => Classical.choose (h2 a)
    constructor
    · ext ⟨a,b⟩
      simp only [mem_graph_iff]
      constructor
      · intro h
-/

theorem Relation.functional_iff_disjoint_preimage_disjoint {r : Relation α β} :
    r.Functional ↔
    (r.domain = Set.univ ∧ ((x y : Set β) → x ∩ y = ∅ → r.preimage x ∩ r.preimage y = ∅)) := by
  constructor
  · intro h
    rw[functional_iff_graph] at h
    obtain ⟨f,rfl⟩ := h
    constructor
    · exact domain_graph
    · intro x y h
      rw[← Set.preimage, ← Set.preimage, ← Set.inter_preimage, h, Function.preimage_empty]
  · intro ⟨h, h'⟩ a
    obtain ⟨b,h''⟩ : a ∈ r.domain := h ▸ Set.mem_univ
    exists b
    constructor
    · exact h''
    · intro y h'''
      by_contra h4
      have : {y} ∩ {b} = (∅ : Set _) := by
        ext
        simp only [Set.mem_inter_iff,
          Set.mem_singleton_iff, Set.not_mem_empty, iff_false, not_and]
        exact fun h => h ▸ h4
      specialize h' _ _ this
      have : a ∈ r.preimage {y} ∩ r.preimage {b} := by
        simp only [Set.mem_inter_iff, mem_preimage_iff, Set.mem_singleton_iff, exists_eq_right, h'', h''', and_true]
      rwa[h'] at this
/-
theorem Relation.functional_iff_comp_inter {r : Relation α β} :
    r.Functional ↔ (r.domain = Set.univ ∧ ∀ (γ : Type*) (s s' : Relation β γ), Relation.comp (s ∩ s') r = s.comp r ∩ s'.comp r) := by
  constructor
  · rintro h
    obtain ⟨f,rfl⟩ := functional_iff_graph.mp h
    constructor
    · simp only [domain_graph]
    · intro γ s s'
      ext ⟨a,c⟩
      simp only [mem_comp_iff, mem_graph_iff, Set.mem_inter_iff, exists_eq_left]
  · rintro ⟨h, h'⟩
    rw[Relation.functional_iff_disjoint_preimage_disjoint]
    constructor
    · exact h
    · intro x y h
      specialize h' PUnit (x.prod Set.univ) (y.prod Set.univ)
      rw[Set.ext_iff] at h'
      rw[← Set.subset_empty_iff]
      intro a ⟨ha, ⟨b, hb1, hb2⟩⟩
      specialize h' ⟨a, PUnit.unit⟩
      replace h' := h'.mp
      simp only [mem_comp_iff, Set.mem_inter_iff, Set.mem_prod_iff, Set.mem_univ, and_true,
        forall_exists_index, and_imp] at h'
      specialize h' b hb1
-/
variable {γ : Type*} {r r' : Relation α β} {s s' : Relation γ α} {a a' : α} {b : β} {c : γ} {x : Set α}

theorem Relation.image_eq_range_inter : r.image x = range (r ∩ (x.prod r.range)) := by
  ext a
  apply exists_congr
  intro a
  simp only [Set.mem_inter_iff, Set.mem_prod_iff, mem_range_iff, and_congr_right_iff, iff_self_and]
  exact fun h h' => ⟨_,h⟩

theorem Relation.image_eq_image_inter_domain : r.image x = r.image (x ∩ r.domain) := by
  ext b
  apply exists_congr
  intro a
  apply and_congr_right
  simp only [Set.mem_inter_iff, mem_domain_iff, iff_self_and]
  exact fun h h' => ⟨_,h⟩
