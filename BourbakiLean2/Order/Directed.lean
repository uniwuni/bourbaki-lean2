import BourbakiLean2.Order.Bounds
import BourbakiLean2.Order.Cofinal
variable {α : Type*}
class RightDirected (α : Type*) [Preorder α] where
  exists_ub : ∀ x y : α, ∃ a, x ≤ a ∧ y ≤ a

noncomputable def RightDirected.ub [Preorder α] [RightDirected α] (x y : α) := Exists.choose (exists_ub x y)


class LeftDirected (α : Type*) [Preorder α] where
  exists_lb : ∀ x y : α, ∃ a, a ≤ x ∧ a ≤ y

noncomputable def LeftDirected.lb [Preorder α] [LeftDirected α] (x y : α) := Exists.choose (exists_lb x y)

section
@[simp] theorem RightDirected.ub_upperBound [Preorder α] [RightDirected α] {x y : α} : UpperBound {x,y} (ub x y) := by
  unfold ub
  have := Exists.choose_spec (exists_ub x y)
  simp only [UpperBound, Set.mem_pair_iff, forall_eq_or_imp, this, forall_eq, and_self]

@[simp] theorem LeftDirected.lb_lowerBound [Preorder α] [LeftDirected α] {x y : α} : LowerBound {x,y} (lb x y) := by
  unfold lb
  have := Exists.choose_spec (exists_lb x y)
  simp only [LowerBound, Set.mem_pair_iff, forall_eq_or_imp, this, forall_eq, and_self]
@[simp] theorem RightDirected.le_ub_left [Preorder α] [RightDirected α] {x y : α} : x ≤ ub x y := RightDirected.ub_upperBound x (Or.inl rfl)
@[simp] theorem RightDirected.le_ub_right [Preorder α] [RightDirected α] {x y : α} : y ≤ ub x y := RightDirected.ub_upperBound y (Or.inr rfl)

@[simp] theorem LeftDirected.lb_le_left [Preorder α] [LeftDirected α] {x y : α} : lb x y ≤ x := LeftDirected.lb_lowerBound x (Or.inl rfl)
@[simp] theorem LeftDirected.lb_le_right [Preorder α] [LeftDirected α] {x y : α} : lb x y ≤ y := LeftDirected.lb_lowerBound y (Or.inr rfl)

def Greatest.rightDirected [Preorder α] {a : α} (h : Greatest a) : RightDirected α :=
  ⟨fun x y => ⟨a, ⟨h x, h y⟩⟩⟩

def Least.leftDirected [Preorder α] {a : α} (h : Least a) : LeftDirected α :=
  ⟨fun x y => ⟨a, ⟨h x, h y⟩⟩⟩

theorem RightDirected.maximal_greatest [PartialOrder α] [RightDirected α] {a : α} (h : Maximal a) : Greatest a := by
  intro b
  have : ub a b = a := h _ le_ub_left
  rw[← this]
  exact le_ub_right

theorem LeftDirected.minimal_least [PartialOrder α] [LeftDirected α] {a : α} (h : Minimal a) : Least a := by
  intro b
  have : lb a b = a := h _ lb_le_left
  rw[← this]
  exact lb_le_right

theorem RightDirected.maximal_iff_greatest [PartialOrder α] [RightDirected α] {a : α} : Maximal a ↔ Greatest a :=
  ⟨RightDirected.maximal_greatest, Greatest.maximal⟩

theorem LeftDirected.minimal_iff_least [PartialOrder α] [LeftDirected α] {a : α} : Minimal a ↔ Least a :=
  ⟨LeftDirected.minimal_least, Least.minimal⟩

theorem rightDirected_op_iff_leftDirected [Preorder α] : RightDirected (Op α) ↔ LeftDirected α := ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩
theorem leftDirected_op_iff_rightDirected [Preorder α] : LeftDirected (Op α) ↔ RightDirected α := ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

instance {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, RightDirected (α i)] : RightDirected (Pointwise ι α) where
  exists_ub x y := by
    conv =>
      arg 1
      intro a
      simp only [LE.le]
      rw[← forall_and]
    apply Classical.axiomOfChoice (r := fun i a => x i ≤ a ∧ y i ≤ a)
    intro i
    apply RightDirected.exists_ub


instance {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, LeftDirected (α i)] : LeftDirected (Pointwise ι α) where
  exists_lb x y := by
    conv =>
      arg 1
      intro a
      simp only [LE.le]
      rw[← forall_and]
    apply Classical.axiomOfChoice (r := fun i a => a ≤ x i ∧ a ≤ y i)
    intro i
    apply LeftDirected.exists_lb

theorem RightDirected.cofinal_subset [Preorder α] [RightDirected α] {s : Set α} (h : Cofinal s) : RightDirected s where
  exists_ub x y := by
    obtain ⟨a,hmem, hle⟩ := h (ub x y)
    exists ⟨a,hmem⟩
    exact ⟨le_trans (α := α) le_ub_left hle, le_trans (α := α) le_ub_right hle⟩

theorem LeftDirected.cofinal_subset [Preorder α] [LeftDirected α] {s : Set α} (h : Coinitial s) : LeftDirected s where
  exists_lb x y := by
    obtain ⟨a,hmem, hle⟩ := h (lb x y)
    exists ⟨a,hmem⟩
    exact ⟨le_trans (α := α) hle lb_le_left, le_trans (α := α) hle lb_le_right⟩




end
