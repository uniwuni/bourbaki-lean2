import BourbakiLean2.Order.MaxMin
variable {α : Type*} [Preorder α]
def Cofinal (s : Set α) := ∀ x, ∃ y ∈ s, x ≤ y
def Coinitial (s : Set α) := ∀ x, ∃ y ∈ s, y ≤ x -- usually not that important

theorem singleton_cofinal_iff_greatest {a : α} : Cofinal {a} ↔ Greatest a := by
  apply forall_congr'
  intro a
  simp only [Set.mem_singleton_iff, exists_eq_left]

theorem singleton_coinitial_iff_least {a : α} : Coinitial {a} ↔ Least a := by
  apply forall_congr'
  intro a
  simp only [Set.mem_singleton_iff, exists_eq_left]

@[simp] theorem Cofinal.univ : Cofinal (Set.univ : Set α) := fun x => ⟨x,True.intro,le_rfl⟩

theorem Cofinal.cofinal_of_subset {s t : Set α} (h : Cofinal s) (h' : s ⊆ t) : Cofinal t := by
  intro x
  obtain ⟨y,h,hh⟩ := h x
  exists y
  exact ⟨h' h, hh⟩
