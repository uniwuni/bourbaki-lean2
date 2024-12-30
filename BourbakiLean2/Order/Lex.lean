import BourbakiLean2.Order.WellOrder

def Lex (ι : Type*) (α : ι → Type*) := (i : ι) → α i

variable {ι : Type*} {α : ι → Type*}
instance [Nonempty ι] [TotalOrder ι] [∀ i, PartialOrder (α i)] : PartialOrder (Lex ι α) where
  le a b := a = b ∨ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i
  le_refl a := Or.inl rfl
  le_trans a b c h1 h2 := by
    rcases h1 with (rfl|h1)
    · exact h2
    · rcases h2 with (rfl|h2)
      · exact Or.inr h1
      · obtain ⟨i,h1i,h1⟩ := h1
        obtain ⟨j,h2j,h2⟩ := h2
        rcases lt_trichotomy i j with (h|rfl|h)
        · right
          exists i
          constructor
          · intro k hk
            specialize h1i _ hk
            specialize h2j _ (lt_of_lt_lt hk h)
            rw[h1i, h2j]
          · specialize h2j _ h
            rw[← h2j]
            assumption
        · right
          exists i
          constructor
          · intro k hk
            rw[h1i _ hk]
            rw[h2j _ hk]
          · exact lt_of_lt_lt h1 h2
        · right
          exists j
          constructor
          · intro k hk
            specialize h2j _ hk
            specialize h1i _ (lt_of_lt_lt hk h)
            rw[h1i, h2j]
          · specialize h1i _ h
            rw[h1i]
            assumption
  le_antisymm a b h1 h2 := by
    rcases h1 with (rfl|h1)
    · rfl
    · rcases h2 with (rfl|h2)
      · rfl
      · obtain ⟨i,h1i,h1⟩ := h1
        obtain ⟨j,h2j,h2⟩ := h2
        apply funext
        intro k
        rcases lt_trichotomy i j with (h|rfl|h)
        · specialize h2j _ h
          rw[h2j] at h1
          exact (not_lt_self h1).elim
        · exact (not_lt_self $ lt_of_lt_lt h1 h2).elim
        · specialize h1i _ h
          rw[h1i] at h2
          exact (not_lt_self h2).elim

instance [Nonempty ι] [WellOrder ι] [∀ i, TotalOrder (α i)] : TotalOrder (Lex ι α) where
  le_total a b := by
    have tri : ∀ i, a i < b i ∨ a i = b i ∨ b i < a i := fun i => lt_trichotomy _ _
    by_cases h : ∀ i, a i = b i
    · exact Or.inl $ Or.inl $ funext h
    rw[Classical.not_forall] at h
    obtain ⟨i,h⟩ := h
    let s := {i | a i < b i ∨ b i < a i}
    have : s.Nonempty := by
      rcases tri i with (h2|h2|h2)
      · exact ⟨i,Or.inl h2⟩
      · exact (h h2).elim
      · exact ⟨i,Or.inr h2⟩
    obtain ⟨i,mem,min⟩ := WellOrder.existsLeast this
    have : ∀ j, j < i → a j = b j := by
      intro j h
      by_contra h'
      rcases tri j with (h3|h3|h3)
      · have : j ∈ s := Or.inl h3
        exact not_lt_self $ lt_of_lt_le h $ min ⟨j,this⟩
      · exact h' h3
      · have : j ∈ s := Or.inr h3
        exact not_lt_self $ lt_of_lt_le h $ min ⟨j,this⟩
    rcases mem with (lt|lt)
    · left
      right
      exists i
    · right
      right
      exists i
      exact ⟨fun i h => (this i h).symm, lt⟩
