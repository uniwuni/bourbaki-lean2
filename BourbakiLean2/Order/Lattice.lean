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
theorem le_inf_of [InfSemilattice α] {x y z : α} (h : z ≤ x) (h' : z ≤ y) : z ≤ x ⊓ y :=
  InfSemilattice.le_inf_of h h'

@[simp] theorem inf_le_left [InfSemilattice α] {x y : α} : x ⊓ y ≤ x := InfSemilattice.inf_le_left
@[simp] theorem inf_le_right [InfSemilattice α] {x y : α} : x ⊓ y ≤ y := InfSemilattice.inf_le_right
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

@[simp] theorem inf_eq_left_iff : x ⊓ y = x ↔ x ≤ y := by
  rw[← le_antisymm_iff]
  simp only [inf_le_left, le_inf_iff, le_rfl, true_and]

@[simp] theorem inf_eq_right_iff : x ⊓ y = y ↔ y ≤ x := by
  rw[← le_antisymm_iff]
  simp only [inf_le_right, le_inf_iff, le_rfl, and_true, true_and]


end

class SupSemilattice (α : Type*) extends PartialOrder α where
  sup : α → α → α
  le_sup_left {x y : α} : x ≤ sup x y
  le_sup_right {x y : α} : y ≤ sup x y
  sup_le_of {x y z : α} (h : x ≤ z) (h' : y ≤ z) : sup x y ≤ z

instance [SupSemilattice α] : Max α where
  max := SupSemilattice.sup
theorem sup_le_of [SupSemilattice α] {x y z : α} (h : x ≤ z) (h' : y ≤ z) : x ⊔ y ≤ z :=
  SupSemilattice.sup_le_of h h'

@[simp] theorem le_sup_left [SupSemilattice α] {x y : α} : x ≤ x ⊔ y := SupSemilattice.le_sup_left
@[simp] theorem le_sup_right [SupSemilattice α] {x y : α} : y ≤ x ⊔ y := SupSemilattice.le_sup_right

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

@[simp] theorem sup_eq_left_iff : x ⊔ y = x ↔ y ≤ x := by
  rw[← le_antisymm_iff]
  simp only [sup_le_iff, le_rfl, true_and, le_sup_left, and_true]

@[simp] theorem sup_eq_right_iff : x ⊔ y = y ↔ x ≤ y := by
  rw[← le_antisymm_iff]
  simp only [sup_le_iff, le_rfl, and_true, le_sup_right]

end

class Lattice (α : Type*) extends InfSemilattice α, SupSemilattice α where

instance {α : Type*} : Lattice (Set α) where
  inf x y := x ∩ y
  sup x y := x ∪ y
  inf_le_left := by simp only [le_set_iff_subset, Set.inter_subset_left, implies_true]
  inf_le_right := by simp only [le_set_iff_subset, Set.inter_subset_right, implies_true]
  le_inf_of x y := Set.subset_inter_iff.mpr ⟨x,y⟩
  sup_le_of x y := Set.union_subset_iff.mpr ⟨x,y⟩
  le_sup_left := by simp only [le_set_iff_subset, Set.subset_union_left, implies_true]
  le_sup_right := by simp only [le_set_iff_subset, Set.subset_union_right, implies_true]
