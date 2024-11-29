import BourbakiLean2.Equivalence

/-- put opposite relation etc on a type -/
def Op (α : Type*) := α
variable {α : Type*}
def toOp (x : α) : Op α := x
def fromOp (x : Op α) : α := x

theorem toOp_fromOp {x : Op α}: toOp (fromOp x) = x := rfl
theorem fromOp_toOp {x : α}: fromOp (toOp x) = x := rfl
instance opLE [LE α] : LE (Op α) where
  le x y := LE.le (α := α) y x

instance opLT [LT α] : LT (Op α) where
  lt x y := LT.lt (α := α) y x

@[simp] theorem toOp_le_iff [LE α] {x y : α} : toOp x ≤ toOp y ↔ y ≤ x := Iff.rfl
@[simp] theorem fromOp_le_iff [LE α] {x y : Op α} : fromOp x ≤ fromOp y ↔ y ≤ x := Iff.rfl
@[simp] theorem toOp_lt_iff [LT α] {x y : α} : toOp x < toOp y ↔ y < x := Iff.rfl
@[simp] theorem fromOp_lt_iff [LT α] {x y : Op α} : fromOp x < fromOp y ↔ y < x := Iff.rfl



/-- extension order for functions -/
structure PartialMap (α : Type*) (β : α → Type*) where
  carrier : Set α
  function : (x : carrier) → β x

variable {α : Type*} {β : α → Type*}
instance piExtendsLE : LE (PartialMap α β) where
  le x y := ∃ h : x.carrier ⊆ y.carrier, ∀ a, (h' : a ∈ x.carrier) → y.function ⟨_, (h h')⟩ = x.function ⟨a,h'⟩

def RelAsLE (_ : Relation α α) := α

instance {r : Relation α α} : LE (RelAsLE r) where
  le x y := (x,y) ∈ r

def RelAsLT (_ : Relation α α) := α

instance {r : Relation α α} : LT (RelAsLT r) where
  lt x y := (x,y) ∈ r

def Pointwise (α : Type*) (β : α → Type*) : Type _ := (x : α) → β x

instance [∀ x, LE (β x)] : LE (Pointwise α β) where
  le f g := ∀ x, f x ≤ g x
