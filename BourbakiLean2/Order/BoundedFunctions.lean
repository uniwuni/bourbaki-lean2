import BourbakiLean2.Order.Bounds

section
variable {α β γ : Type*} [Preorder β]

def Function.BoundedBelow (f : α → β) := Set.BoundedBelow (f '' Set.univ)
def Function.BoundedAbove (f : α → β) := Set.BoundedAbove (f '' Set.univ)
def Function.Bounded (f : α → β) := Set.Bounded (f '' Set.univ)

variable {f : α → β} {g : β → γ}
@[simp] theorem Function.boundedBelow_iff : f.BoundedBelow ↔ ∃x, ∀a, x ≤ f a := by
  apply exists_congr
  intro b
  unfold LowerBound
  simp only [Set.mem_image_iff, Set.mem_univ, and_true, forall_exists_index,
    forall_eq_apply_imp_iff]

@[simp] theorem Function.boundedAbove_iff : f.BoundedAbove ↔ ∃x, ∀a, f a ≤ x := by
  apply exists_congr
  intro b
  unfold UpperBound
  simp only [Set.mem_image_iff, Set.mem_univ, and_true, forall_exists_index,
    forall_eq_apply_imp_iff]

@[simp] theorem Function.bounded_iff_above_below : f.Bounded ↔ (f.BoundedAbove ∧ f.BoundedBelow) := Iff.rfl

theorem Function.bounded_iff : f.Bounded ↔ ∃x y, ∀a, f a ≤ x ∧ y ≤ f a := by
  simp only [bounded_iff_above_below, boundedAbove_iff, boundedBelow_iff]
  constructor
  · exact fun ⟨⟨x,h⟩,⟨y,h'⟩⟩ => ⟨x,⟨y, fun a => ⟨h a, h' a⟩⟩⟩
  · exact fun ⟨x,⟨y,h⟩⟩ => ⟨⟨x, fun a => (h a).1⟩,⟨y, fun a => (h a).2⟩⟩
end
section
variable {α β γ : Type*} {f : β → γ} (g : α → β) [Preorder γ]

theorem Function.BoundedBelow.comp (h : f.BoundedBelow) : (f ∘ g).BoundedBelow := by
  simp only [boundedBelow_iff, comp_apply] at *
  obtain ⟨x, h⟩ := h
  exists x
  exact fun a => h $ g a

theorem Function.BoundedAbove.comp (h : f.BoundedAbove) : (f ∘ g).BoundedAbove := by
  simp only [boundedAbove_iff, comp_apply] at *
  obtain ⟨x, h⟩ := h
  exists x
  exact fun a => h $ g a

theorem Function.Bounded.comp (h : f.Bounded) : (f ∘ g).Bounded := by
  rw[Function.bounded_iff_above_below] at *
  exact ⟨h.1.comp _, h.2.comp _⟩

end
section
variable {α : Type*} [Preorder α]
theorem boundedBelow_iff_val_boundedBelow {t : Set α} : t.BoundedBelow ↔ (Subtype.val : t → α).BoundedBelow := by
  rw[Function.BoundedBelow]
  simp only [Subtype.val_image]

theorem boundedAbove_iff_val_boundedAbove {t : Set α} : t.BoundedAbove ↔ (Subtype.val : t → α).BoundedAbove := by
  rw[Function.BoundedAbove]
  simp only [Subtype.val_image]

theorem bounded_iff_val_bounded {t : Set α} : t.Bounded ↔ (Subtype.val : t → α).Bounded := by
  rw[Function.Bounded]
  simp only [Subtype.val_image]

end
