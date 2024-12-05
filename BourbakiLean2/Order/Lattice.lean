import BourbakiLean2.Order.Directed
import BourbakiLean2.Order.GlbLub


@[inherit_doc]
infixl:68 " ⊔ " => Max.max

@[inherit_doc]
infixl:69 " ⊓ " => Min.min

variable {α : Type*}
class InfSemilattice (α : Type*) extends PartialOrder α where
  inf : α → α → α
  inf_le_left {x y : α} : inf x y ≤ x
  inf_le_right {x y : α} : inf x y ≤ y
  le_inf_of {x y z : α} (h : z ≤ x) (h' : z ≤ y) : z ≤ inf x y

instance [InfSemilattice α] : Min α where
  min := InfSemilattice.inf
export InfSemilattice (inf_le_left inf_le_right le_inf_of)

class SupSemilattice (α : Type*) extends PartialOrder α where
  sup : α → α → α
  le_sup_left {x y : α} : x ≤ sup x y
  le_sup_right {x y : α} : y ≤ sup x y
  sup_le_of {x y z : α} (h : x ≤ z) (h' : y ≤ z) : sup x y ≤ z

instance [SupSemilattice α] : Max α where
  max := SupSemilattice.sup
export SupSemilattice (le_sup_left le_sup_right sup_le_of)

instance [InfSemilattice α] : LeftDirected α where
  exists_lb x y := ⟨x ⊓ y, inf_le_left, inf_le_right⟩

instance [SupSemilattice α] : RightDirected α where
  exists_ub x y := ⟨x ⊔ y, le_sup_left, le_sup_right⟩
