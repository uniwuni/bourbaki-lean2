import BourbakiLean2.Order.TotalOrder
variable {α β : Type*} {x y z : α}

class WellOrder (α : Type*) extends TotalOrder α where
  existsLeast {s : Set α} (h : s.Nonempty) : ∃ a, ∃ h : a ∈ s, Least (⟨a,h⟩ : s)
