import BourbakiLean2.Order.Inductive

variable {α β : Type*} [WellOrder α] [WellOrder β]

theorem WellOrder.either_embeds :
    (∃ x : InitialSegment β, ∃ f : α → x.val, IsOrderIso f) ∨ (∃ x : InitialSegment α, ∃ f : x.val → β, IsOrderIso f) := by
