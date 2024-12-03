import BourbakiLean2.Order.Basic
variable {ι : Type*} {x : ι → Type*}

instance [PartialOrder ι] [∀ i, Preorder (x i)] : Preorder (Sigma x) where
  le := fun ⟨i,a⟩ ⟨j,b⟩ => i < j ∨ (∃ (h : i = j), h ▸ a ≤ b)
  le_refl a := Or.inr ⟨rfl,le_rfl⟩
  le_trans := fun ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ h h' => by
    rcases h with (h|⟨rfl,h⟩)
    · rcases h' with (h'|⟨rfl, h'⟩)
      · exact Or.inl $ lt_of_lt_lt h h'
      · exact Or.inl h
    · rcases h' with (h'|⟨rfl, h'⟩)
      · exact Or.inl h'
      · exact Or.inr  ⟨rfl, le_trans h h'⟩

instance [PartialOrder ι] [∀ i, PartialOrder (x i)] : PartialOrder (Sigma x) where
  le_antisymm := fun ⟨i,a⟩ ⟨j,b⟩ h h' => by
    rcases h with (h|⟨rfl,h⟩)
    · rcases h' with (h'|⟨rfl,h'⟩)
      · apply (not_lt_self $ lt_of_lt_lt h h').elim
      · apply (not_lt_self h).elim
    · rcases h' with (h'|⟨eq,h'⟩)
      · apply (not_lt_self h').elim
      · rcases eq
        congr
        apply le_antisymm h h'
