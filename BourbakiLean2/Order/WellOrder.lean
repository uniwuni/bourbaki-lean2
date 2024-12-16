import BourbakiLean2.Order.TotalOrder
variable {α β : Type*} {x y z : α}

class WellOrder (α : Type*) extends TotalOrder α where
  existsLeast {s : Set α} (h : s.Nonempty) : ∃ a, ∃ h : a ∈ s, Least (⟨a,h⟩ : s)

instance: WellOrder Empty where
  existsLeast h := by rcases h with ⟨⟨⟩,h⟩

instance: WellOrder Unit where
  existsLeast h := by
    rcases h with ⟨⟨⟩,h⟩
    exists PUnit.unit
    simp only [Least, le_rfl, implies_true, exists_const, h]

instance [WellOrder α] {p : α → Prop} : WellOrder {x // p x} where
  existsLeast {s} h := by
    rcases h with ⟨⟨a,h⟩,h'⟩
    have ⟨a,⟨hp,hs⟩,hl⟩ := WellOrder.existsLeast (s := {x | ∃ h, ⟨x,h⟩ ∈ s}) ⟨a,h,h'⟩
    exists ⟨a,hp⟩
    exists hs
    simp only [Least, Subtype.le_iff_val, Subtype.forall]
    intro b hbp hbs
    exact hl ⟨b,hbp,hbs⟩

instance [WellOrder α] : WellOrder (AdjoinGreatest α) where
  existsLeast {s} h' := by
    by_cases h : ∃ a, AdjoinGreatest.to a ∈ s
    · rcases h with ⟨a,ha⟩
      let t := Set.preimage AdjoinGreatest.to s
      have ⟨a,ha,hleast⟩ := WellOrder.existsLeast (s := t) ⟨a, Set.mem_preimage_iff.mpr ha⟩
      exists AdjoinGreatest.to a
      exists Set.mem_preimage_iff.mp ha
      intro ⟨b,hb⟩
      rcases b with (b|b)
      · simp only [Subtype.le_iff_val, ge_iff_le]
        exact hleast ⟨b,Set.mem_preimage_iff.mpr hb⟩
      · trivial
    · obtain ⟨(a|a), ha⟩ := h'
      · exact (h ⟨_,ha⟩).elim
      · exists AdjoinGreatest.greatest
        rcases a
        exists ha
        rintro ⟨(b|b),hb⟩
        · exact (h ⟨_,hb⟩).elim
        · trivial

def totalOrder_of_exists_least [PartialOrder α] (h : ∀ {s : Set α} (_ : s.Nonempty), ∃ a, ∃ h : a ∈ s, Least (⟨a,h⟩ : s)) :
    TotalOrder α where
  le_total x y := by
    obtain ⟨a,(rfl|rfl), least⟩ := h (s := {x,y}) ⟨x, Or.inl rfl⟩
    · simp only [Least, Subtype.le_iff_val, Subtype.forall, Set.mem_pair_iff, forall_eq_or_imp,
      le_rfl, forall_eq, true_and] at least
      left
      assumption
    · simp only [Least, Subtype.le_iff_val, Subtype.forall, Set.mem_pair_iff, forall_eq_or_imp,
      forall_eq, le_rfl, and_true] at least
      right
      assumption

namespace WellOrder
variable [WellOrder α]
theorem hasLUB_of_bounded_above {s : Set α} (h : s.BoundedAbove) : ∃ x, IsLUB s x := by
  let t := {a | UpperBound s a}
  have h : t.Nonempty := h
  have ⟨a, h, least⟩ := existsLeast h
  exact ⟨a,⟨h,least⟩⟩

end WellOrder
