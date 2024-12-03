import BourbakiLean2.Order.Monotone

variable {α β : Type*} {r : Relation α α}
instance [LE α] : LE (Quot (Function.curry r)) where
  le a b := ∀ x, Quot.mk _ x = a → ∃ y, Quot.mk _ y = b ∧ x ≤ y

instance {α : Type*} {r : Relation α α} [r.IsEquivalence] [Preorder α] : Preorder (Quot (Function.curry r)) where
  le_refl a := fun x h => ⟨x,h,le_refl x⟩
  le_trans a b c h h' := by
    intro x' h''
    obtain ⟨x,rfl⟩ := a.exists_rep
    obtain ⟨y,rfl⟩ := b.exists_rep
    obtain ⟨z,rfl⟩ := c.exists_rep
    rw[← h''] at h
    replace ⟨y', h⟩ := h x' rfl
    replace ⟨z', h'⟩ := h' y' h.1
    exists z'
    exact ⟨h'.1, le_trans h.2 h'.2⟩

theorem Quot.monotone_of_comp_monotone [LE α] [LE β] {g : Quot (Function.curry r) → β} (h : Monotone (g ∘ Quot.mk _)) : Monotone g := by
  intro a b h'
  obtain ⟨x,rfl⟩ := a.exists_rep
  obtain ⟨y,rfl⟩ := b.exists_rep
  obtain ⟨y',eq,ord⟩ := h' x rfl
  rw[← eq]
  apply h ord


theorem Quot.mk_monotone_iff [Preorder α] :
    Monotone (Quot.mk (Function.curry r)) ↔
      (∀ x x' y : α, x ≤ y →
                     Quot.mk (Function.curry r) x' = Quot.mk _ x →
                     ∃ y', Quot.mk (Function.curry r) y' = Quot.mk _ y ∧ x' ≤ y'):= by
  constructor
  · intro h x x' y le eq
    exact h le x' eq
  · intro h x y le x' eq
    exact h x x' y le eq

def WeaklyOrderCompatible [Preorder α] (r : Relation α α) := Monotone (Quot.mk (Function.curry r))

theorem weaklyOrderCompatible_product_collapse [Preorder α] [Preorder β] :
    WeaklyOrderCompatible (Function.identified_under (Prod.fst : α × β → α)) := by
  intro ⟨a,b⟩ ⟨a',b'⟩ ⟨h,h'⟩ ⟨a'',b''⟩ eq
  simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under] at eq
  rw[eq]
  exists (a',b'')
  simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under, true_and]
  exact ⟨h, le_rfl⟩

theorem prod_quotient_order_iso [Preorder α] [Preorder β] {b : β} :
    IsOrderIso (fun x : α => Quot.mk (Function.curry $ Function.identified_under (Prod.fst : α × β → α)) (x, b)) := by
  have bij : Function.Bijective (fun x : α => Quot.mk (Function.curry $ Function.identified_under (Prod.fst : α × β → α)) (x, b)) := by
    constructor
    · simp only [Function.Injective, Quot.mk_eq_iff_rel, Function.mem_identified_under, imp_self,
      implies_true]
    · rw[Function.surj_iff]
      intro b'
      obtain ⟨⟨a,b'⟩, rfl⟩ := b'.exists_rep
      exists a
      simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under]
  constructor
  pick_goal 3
  · exact bij
  · intro x y h
    have : (x,b) ≤ (y,b) := ⟨h, le_rfl⟩
    apply weaklyOrderCompatible_product_collapse this
  · apply Quot.monotone_of_comp_monotone
    intro ⟨a,c⟩ ⟨a',c'⟩ ⟨aa',cc'⟩
    have : (bij.inv ∘ Quot.mk (Function.curry (Function.identified_under Prod.fst))) (a,c) = a := by
      simp only [Function.comp_apply, Function.Bijective.inv_val_iff, Quot.mk_eq_iff_rel,
        Function.mem_identified_under]
    rw[this]
    have : (bij.inv ∘ Quot.mk (Function.curry (Function.identified_under Prod.fst))) (a',c') = a' := by
      simp only [Function.comp_apply, Function.Bijective.inv_val_iff, Quot.mk_eq_iff_rel,
        Function.mem_identified_under]
    rw[this]
    exact aa'

instance Quot.partialOrder_of [PartialOrder α] [r.IsEquivalence]
    (h' : ∀ x y z, x ≤ y → y ≤ z → Quot.mk (Function.curry r) x = Quot.mk _ z → Quot.mk (Function.curry r) x = Quot.mk _ y)
    : PartialOrder (Quot (Function.curry r)) where
  le_antisymm a b le ge := by
    obtain ⟨x,rfl⟩ := a.exists_rep
    obtain ⟨y,rfl⟩ := b.exists_rep
    obtain ⟨y',eqy,ordy⟩ := le x rfl
    obtain ⟨x',eqx,ordx⟩ := ge y' eqy
    rw[h' x y' x' ordy ordx eqx.symm, eqy]

theorem Monotone.partialOrder_condition_quot {f : α → β} [Preorder α] [PartialOrder β] (h : Monotone f) {x y z}
    (xy : x ≤ y) (yz : y ≤ z) (eq : Quot.mk (Function.curry f.identified_under) x = Quot.mk _ z) :
    Quot.mk (Function.curry f.identified_under) x = Quot.mk _ y := by
  simp only [Monotone, Quot.mk_eq_iff_rel, Function.mem_identified_under] at *
  apply le_antisymm
  · apply h xy
  · rw[eq]
    apply h yz

theorem Monotone.identifiedUnder_weaklyOrderCompatible_iff {f : α → β} [Preorder α] [Preorder β] (h : Monotone f) :
    WeaklyOrderCompatible f.identified_under ↔ (∀ x x' y, x ≤ y → f x' = f x → ∃y', f y' = f y ∧ x' ≤ y'):= by
  unfold WeaklyOrderCompatible
  rw[Quot.mk_monotone_iff]
  simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under]
