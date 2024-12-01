import BourbakiLean2.Order.Bounds

def IsGLB {α : Type*} [Preorder α] (s : Set α) (a : α) := ∃ (h : LowerBound s a), Greatest (⟨a,h⟩ : {a : α // LowerBound s a})
def IsLUB {α : Type*} [Preorder α] (s : Set α) (a : α) := ∃ (h : UpperBound s a), Least (⟨a,h⟩ : {a : α // UpperBound s a})

section
variable {α : Type*} [Preorder α] {s : Set α} {a : α}
@[simp] theorem isGLB_iff : IsGLB s a ↔ (LowerBound s a ∧ ∀ b, LowerBound s b → b ≤ a) := by
  unfold IsGLB
  simp only [Greatest, Subtype.le_iff_val, Subtype.forall, exists_prop]

@[simp] theorem isLUB_iff : IsLUB s a ↔ (UpperBound s a ∧ ∀ b, UpperBound s b → a ≤ b) := by
  unfold IsLUB
  simp only [Least, Subtype.le_iff_val, Subtype.forall, exists_prop, and_congr_right_iff]

theorem Least.isGLB_of_mem {a : s} (h : Least a) : IsGLB s a.val := by
  rcases a with ⟨a,mem⟩
  rw [isGLB_iff]
  have := (lowerBound_iff_least_of_mem mem).mp h
  apply And.intro this
  intro b hlb
  apply hlb _ mem

theorem Greatest.isLUB_of_mem {a : s} (h : Greatest a) : IsLUB s a.val := by
  rcases a with ⟨a,mem⟩
  rw [isLUB_iff]
  have := (upperBound_iff_greatest_of_mem mem).mp h
  apply And.intro this
  intro b hlb
  apply hlb _ mem

@[simp] theorem op_isGLB_iff : IsGLB (α := Op α) s (toOp a) ↔ IsLUB s a := Iff.rfl
@[simp] theorem op_isLUB_iff : IsLUB (α := Op α) s (toOp a) ↔ IsGLB s a := Iff.rfl

end
section
variable {α : Type*} [PartialOrder α] {s : Set α} {a : α}

theorem IsGLB.all_eq {b : α} (h : IsGLB s a) (h' : IsGLB s b) : a = b := by
  have := Greatest.all_eq (α := {a : α // LowerBound s a}) h.2 h'.2
  rwa[Subtype.eq_iff] at this

theorem IsLUB.all_eq {b : α} (h : IsLUB s a) (h' : IsLUB s b) : a = b := by
  have := Least.all_eq (α := {a : α // UpperBound s a}) h.2 h'.2
  rwa[Subtype.eq_iff] at this

instance : Subsingleton {a : α // IsGLB s a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'
instance : Subsingleton {a : α // IsLUB s a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'

end
