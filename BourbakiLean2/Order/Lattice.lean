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

attribute [simp] InfSemilattice.inf_le_left
attribute [simp] InfSemilattice.inf_le_right

instance [InfSemilattice α] : Min α where
  min := InfSemilattice.inf
export InfSemilattice (inf_le_left inf_le_right le_inf_of)


section
variable [InfSemilattice α] {x y z w : α}
instance : LeftDirected α where
  exists_lb x y := ⟨x ⊓ y, inf_le_left, inf_le_right⟩

theorem inf_isGLB : IsGLB {x,y} (x ⊓ y) := by
  constructor
  swap
  · intro a h'
    rcases h' with (rfl|rfl)
    · exact inf_le_left
    · exact inf_le_right
  · rintro ⟨a,h⟩
    apply le_inf_of (h x $ Or.inl rfl) (h y $ Or.inr rfl)

@[simp] theorem inf_monotone_left : Monotone (fun y => x ⊓ y) :=
  fun _ _ h => le_inf_of inf_le_left (le_trans inf_le_right h)

@[simp] theorem inf_monotone_right : Monotone (fun x => x ⊓ y) :=
  fun _ _ h => le_inf_of (le_trans inf_le_left h) inf_le_right

theorem inf_monotone (h : x ≤ y) (h' : z ≤ w) : x ⊓ z ≤ y ⊓ w :=
  le_trans (inf_monotone_right h) (inf_monotone_left h')

@[simp] theorem inf_self : x ⊓ x = x := le_antisymm inf_le_left (le_inf_of le_rfl le_rfl)
@[simp] theorem le_inf_iff : z ≤ x ⊓ y ↔ (z ≤ x ∧ z ≤ y) :=
  ⟨fun h => ⟨le_trans h inf_le_left, le_trans h inf_le_right⟩, fun ⟨h,h'⟩ => le_inf_of h h'⟩

theorem inf_comm : x ⊓ y = y ⊓ x := le_antisymm (le_inf_of inf_le_right inf_le_left) (le_inf_of inf_le_right inf_le_left)
theorem inf_assoc : x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z := by
  apply le_antisymm
  · apply le_inf_of (le_inf_of inf_le_left $ le_trans inf_le_right inf_le_left) $ le_trans inf_le_right inf_le_right
  · apply le_inf_of (le_trans inf_le_left inf_le_left) (le_inf_of (le_trans inf_le_left inf_le_right) inf_le_right)

end

class SupSemilattice (α : Type*) extends PartialOrder α where
  sup : α → α → α
  le_sup_left {x y : α} : x ≤ sup x y
  le_sup_right {x y : α} : y ≤ sup x y
  sup_le_of {x y z : α} (h : x ≤ z) (h' : y ≤ z) : sup x y ≤ z

instance [SupSemilattice α] : Max α where
  max := SupSemilattice.sup
export SupSemilattice (le_sup_left le_sup_right sup_le_of)


section
variable [SupSemilattice α] {x y z w : α}

instance : RightDirected α where
  exists_ub x y := ⟨x ⊔ y, le_sup_left, le_sup_right⟩

theorem sup_isLUB : IsLUB {x,y} (x ⊔ y) := by
  constructor
  swap
  · intro a h'
    rcases h' with (rfl|rfl)
    · exact le_sup_left
    · exact le_sup_right
  · rintro ⟨a,h⟩
    apply sup_le_of (h x $ Or.inl rfl) (h y $ Or.inr rfl)

@[simp] theorem sup_monotone_left : Monotone (fun y => x ⊔ y) :=
  fun _ _ h => sup_le_of le_sup_left (le_trans h le_sup_right)

@[simp] theorem sup_monotone_right : Monotone (fun x => x ⊔ y) :=
  fun _ _ h => sup_le_of (le_trans h le_sup_left) le_sup_right

theorem sup_monotone (h : x ≤ y) (h' : z ≤ w) : x ⊔ z ≤ y ⊔ w :=
  le_trans (sup_monotone_right h) (sup_monotone_left h')

@[simp] theorem sup_self : x ⊔ x = x := le_antisymm (sup_le_of le_rfl le_rfl) le_sup_left
@[simp] theorem sup_le_iff : x ⊔ y ≤ z ↔ (x ≤ z ∧ y ≤ z) :=
  ⟨fun h => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩, fun ⟨h,h'⟩ => sup_le_of h h'⟩

theorem sup_comm : x ⊔ y = y ⊔ x := le_antisymm (sup_le_of le_sup_right le_sup_left) (sup_le_of le_sup_right le_sup_left)
theorem sup_assoc : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  apply le_antisymm
  · apply sup_le_of (le_trans le_sup_left le_sup_left) $ sup_le_of (le_trans le_sup_right le_sup_left) le_sup_right
  · apply sup_le_of (sup_le_of le_sup_left $ le_trans le_sup_left le_sup_right) $ le_trans le_sup_right le_sup_right

end
