import BourbakiLean2.Order.Monotone
variable {α β : Type*}
structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function of an `OrderHom`. -/
  toFun : α → β
  /-- The underlying function of an `OrderHom` is monotone. -/
  monotone : Monotone toFun

theorem OrderHom.eq_iff [Preorder α] [Preorder β] {f g : OrderHom α β} : f = g ↔ f.toFun = g.toFun := by
  constructor
  · rintro rfl
    rfl
  · rcases f
    rcases g
    simp only [mk.injEq, imp_self]

infixr:25 " →o " => OrderHom

instance [Preorder α] [Preorder β] : CoeFun (OrderHom α β) (fun _ => α → β) where
  coe := OrderHom.toFun

instance [Preorder α] [Preorder β] : Preorder (α →o β) where
  le x y := LE.le (α := Pointwise α (fun _ => β)) x.toFun y.toFun
  le_refl x := le_refl (α := Pointwise _ _) x.toFun
  le_trans x y z h h' := le_trans (α := Pointwise α (fun _ => β)) h h'

instance [Preorder α] [PartialOrder β] : PartialOrder (α →o β) where
  le_antisymm x _ h h' := (x.eq_iff).mpr $ le_antisymm (α := Pointwise α (fun _ => β)) h h'
