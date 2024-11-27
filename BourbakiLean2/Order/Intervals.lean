import BourbakiLean2.Order.Monotone

variable {α : Type*} [Preorder α]

/-- The interval [a, ∞). -/
def Set.Ici (a : α) : Set α := {b | a ≤ b}
@[simp] theorem Set.mem_Ici_iff {a b : α} : b ∈ Set.Ici a ↔ a ≤ b := Iff.rfl
@[simp high] theorem Set.mem_Ici_self {a : α} : a ∈ Set.Ici a := le_refl _
theorem Set.Ici_antitone : Antitone (Set.Ici (α := α)) := fun _ _ h _ => le_trans h
theorem Set.Ici_strictAnti : StrictAntitone (Set.Ici (α := α)) := by
  intro a b h
  rw[lt_iff_le_not_le] at *
  apply And.intro $ Set.Ici_antitone h.1
  intro h'
  exact h.2 $ h' mem_Ici_self

/-- The interval (-∞, a]. -/
def Set.Iic (a : α) : Set α := {b | b ≤ a}
@[simp] theorem Set.mem_Iic_iff {a b : α} : b ∈ Set.Iic a ↔ b ≤ a := Iff.rfl
@[simp high] theorem Set.mem_Iic_self {a : α} : a ∈ Set.Iic a := le_refl _
theorem Set.Iic_monotone : Monotone (Set.Iic (α := α)) := fun _ _ h _ h' => le_trans h' h
theorem Set.Iic_strictMono : StrictMonotone (Set.Iic (α := α)) := by
  intro a b h
  rw[lt_iff_le_not_le] at *
  apply And.intro $ Set.Iic_monotone h.1
  intro h'
  exact h.2 $ h' mem_Ici_self
