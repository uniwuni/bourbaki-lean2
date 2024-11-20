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
