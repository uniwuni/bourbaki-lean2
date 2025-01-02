import BourbakiLean2.Set.Cardinal
universe u
variable {α ι : Type u}

class Cardinal.Finite (a : Cardinal.{u}) where
  neq_plus_one : a ≠ a + 1

theorem Cardinal.finite_iff {a : Cardinal.{u}} : a.Finite ↔ a ≠ a + 1 := by
  constructor
  · intro h
    exact h.neq_plus_one
  · intro h
    constructor
    · exact h

@[simp] def FiniteCardinal := {a : Cardinal.{u} // a.Finite}
def Finite (α : Type u) := Cardinal.Finite (Cardinal.mk α)
@[simp] def FiniteType := {α : Type u // Finite α}
def FiniteType.cardinality' : FiniteType.{u} → FiniteCardinal.{u} := fun ⟨x,h⟩ => ⟨Cardinal.mk x, h⟩

theorem Cardinal.finite_iff_add_one_finite {a : Cardinal.{u}} : (a + 1).Finite ↔ a.Finite := by
  simp only [finite_iff, ne_eq]
  apply not_congr
  constructor
  · apply Cardinal.sum_one_cancel
  · intro h
    rw[← h, ← h]

instance {a : Cardinal.{u}} [h : a.Finite] : (a + 1).Finite := by
  rw[Cardinal.finite_iff_add_one_finite]
  exact h

instance : (0 : Cardinal.{u}).Finite := by
  constructor
  intro h
  rw[Cardinal.zero_add] at h
  exact Cardinal.zero_neq_one h

instance h : (1 : Cardinal.{u}).Finite := by
  rw[← Cardinal.zero_add (a := 1)]
  infer_instance
