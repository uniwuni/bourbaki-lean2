import BourbakiLean2.Order.Basic
import BourbakiLean2.Order.Synonyms
variable {α β : Type*}
section Defs
variable (f : α → β)
@[simp] def Monotone [LE α] [LE β] := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
@[simp] def Antitone [LE α] [LE β] := ∀ ⦃a b⦄, a ≤ b → f b ≤ f a
@[simp] def StrictMonotone [LT α] [LT β] := ∀ ⦃a b⦄, a < b → f a < f b
@[simp] def StrictAntitone [LT α] [LT β] := ∀ ⦃a b⦄, a < b → f b < f a

structure IsOrderIso [LE α] [LE β] where
  bij : f.Bijective
  monotone : Monotone f
  monotone_inv : Monotone bij.inv

end Defs

section CategoryStuff
variable {γ : Type*} {f : β → γ} {g : α → β}

section
variable [LE α] [LE β] [LE γ]
@[simp] theorem id_mono : Monotone (id : α → α) := fun _ _ h => h
theorem Monotone.comp (h : Monotone f) (h' : Monotone g) : Monotone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem Monotone.comp_anti (h : Monotone f) (h' : Antitone g) : Antitone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem Monotone.restrict {x : Set β} (h : Monotone f) : Monotone (f.restriction x) :=
  fun _ _ h' => h h'

theorem Antitone.comp (h : Antitone f) (h' : Antitone g) : Monotone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem Antitone.comp_mono (h : Antitone f) (h' : Monotone g) : Antitone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem Antitone.restrict {x : Set β} (h : Antitone f) : Antitone (f.restriction x) :=
  fun _ _ h' => h h'

theorem isOrderIso_iff_reflect : IsOrderIso f ↔ f.Bijective ∧ Monotone f ∧ (∀ x y, f x ≤ f y → x ≤ y) := by
  constructor
  · intro h
    constructor
    · exact h.bij
    · constructor
      · exact h.monotone
      · intro x y le
        have := h.monotone_inv le
        simp only [Function.Bijective.inv_val_val] at this
        exact this
  · intro ⟨h1,h2,h3⟩
    constructor
    · assumption
    swap
    · assumption
    · intro x y h
      rw[← h1.val_inv_val (b := x), ← h1.val_inv_val (b := y)] at h
      apply h3 _ _ h

theorem IsOrderIso.le_iff (h : IsOrderIso f) {a b : β} : f a ≤ f b ↔ a ≤ b := by
  constructor
  · intro h'
    replace h' := h.monotone_inv h'
    simp only [Function.Bijective.inv_val_val] at h'
    assumption
  · apply h.monotone

theorem IsOrderIso.inv (h : IsOrderIso f) : IsOrderIso h.bij.inv where
  bij := h.bij.inv_bij
  monotone := h.monotone_inv
  monotone_inv := h.bij.inv_inv.symm ▸ h.monotone

theorem IsOrderIso.comp (h : IsOrderIso f) (h' : IsOrderIso g) : IsOrderIso (f ∘ g) where
  bij := h.bij.comp h'.bij
  monotone := h.monotone.comp h'.monotone
  monotone_inv := h.bij.comp_inv h'.bij ▸ h'.monotone_inv.comp h.monotone_inv

end
section
variable [LT α] [LT β] [LT γ]
@[simp] theorem id_strict_mono : StrictMonotone (id : α → α) := fun _ _ h => h
theorem StrictMonotone.comp (h : StrictMonotone f) (h' : StrictMonotone g) : StrictMonotone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem StrictMonotone.comp_strictAnti (h : StrictMonotone f) (h' : StrictAntitone g) : StrictAntitone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem StrictAntitone.comp (h : StrictAntitone f) (h' : StrictAntitone g) : StrictMonotone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem StrictAntitone.comp_mono (h : StrictAntitone f) (h' : StrictMonotone g) : StrictAntitone (f ∘ g) :=
  fun _ _ h'' => h $ h' h''

theorem StrictMonotone.restrict {x : Set β} (h : StrictMonotone f) : StrictMonotone (f.restriction x) :=
  fun _ _ h' => h h'

theorem StrictAntitone.restrict {x : Set β} (h : StrictAntitone f) : StrictAntitone (f.restriction x) :=
  fun _ _ h' => h h'


end
end CategoryStuff
section PreorderImps
variable [LE α] [Preorder β] {f : α → β}
@[simp] theorem const_mono {b : β} : Monotone (Function.const α b) := fun _ _ _ => le_refl _
@[simp] theorem const_anti {b : β} : Antitone (Function.const α b) := fun _ _ _ => le_refl _
end PreorderImps

section PartialOrderImps
variable [PartialOrder α] [PartialOrder β] {f : α → β}
theorem StrictMonotone.monotone (h : StrictMonotone f) : Monotone f := by
  intro x y h'
  rw[le_iff_lt_or_eq] at h'
  rcases h' with (h'|rfl)
  · exact le_of_lt $ h h'
  · rfl

theorem Monotone.strictMono_of_inj (h : Monotone f) (h' : f.Injective) : StrictMonotone f := by
  intro _ _ h''
  rw[lt_iff_le_not_eq] at *
  apply And.intro $ h h''.1
  apply Function.inj_iff_neq_of_neq.mp h' _ _ h''.2

theorem Antitone.strictAnti_of_inj (h : Antitone f) (h' : f.Injective) : StrictAntitone f := by
  intro _ _ h''
  rw[lt_iff_le_not_eq] at *
  apply And.intro $ h h''.1
  apply Ne.symm $ Function.inj_iff_neq_of_neq.mp h' _ _ h''.2

end PartialOrderImps

section Op
variable {f : α → β}

@[simp] theorem toOp_antitone [LE α] : Antitone (toOp : α → Op α) := fun _ _ => id
@[simp] theorem toOp_strictAnti [LT α] : StrictAntitone (toOp : α → Op α) := fun _ _ => id
@[simp] theorem fromOp_antitone [LE α] : Antitone (fromOp : Op α → α) := fun _ _ => id
@[simp] theorem fromOp_strictAnti [LT α] : StrictAntitone (fromOp : Op α → α) := fun _ _ => id

theorem monotone_iff_toOp_antitone [LE α] [LE β] : Monotone f ↔ Antitone (toOp ∘ f) := Iff.rfl
theorem monotone_iff_fromOp_antitone [LE α] [LE β] : Monotone f ↔ Antitone (f ∘ fromOp) := by
  constructor
  · exact fun h _ _ h' => h $ fromOp_antitone h'
  · exact fun h _ _ h' => toOp_antitone $ h h'

theorem antitone_iff_toOp_monotone [LE α] [LE β] : Antitone f ↔ Monotone (toOp ∘ f) := Iff.rfl
theorem antitone_iff_fromOp_monotone [LE α] [LE β] : Antitone f ↔ Monotone (f ∘ fromOp) := by
  constructor
  · exact fun h _ _ h' => h $ fromOp_antitone h'
  · exact fun h _ _ h' => toOp_antitone $ h h'

theorem strictMono_iff_toOp_strictAnti [LT α] [LT β] : StrictMonotone f ↔ StrictAntitone (toOp ∘ f) := Iff.rfl
theorem strictMono_iff_fromOp_strictAnti [LT α] [LT β] : StrictMonotone f ↔ StrictAntitone (f ∘ fromOp) := by
  constructor
  · exact fun h _ _ h' => h $ fromOp_strictAnti h'
  · exact fun h _ _ h' => toOp_strictAnti $ h h'

theorem strictAnti_iff_toOp_strictMono [LT α] [LT β] : StrictAntitone f ↔ StrictMonotone (toOp ∘ f) := Iff.rfl
theorem strictAnti_iff_fromOp_strictMono [LT α] [LT β] : StrictAntitone f ↔ StrictMonotone (f ∘ fromOp) := by
  constructor
  · exact fun h _ _ h' => h $ fromOp_strictAnti h'
  · exact fun h _ _ h' => toOp_strictAnti $ h h'

end Op

@[simp] theorem Set.compl_strictAnti : StrictAntitone (Set.compl : Set α → Set α) := by
  intro a b h
  rw[lt_iff_le_not_eq] at *
  simp only [le_set_iff_subset] at *
  refine And.intro ?wah $ Function.inj_iff_neq_of_neq.mp (fun _ _ => compl_inj) _ _ h.2.symm
  rw[compl_subset_iff_compl_subset, compl_compl]
  exact h.1

theorem pseudoinv_of_antitone [Preorder α] [PartialOrder β] {f : α → β} {g : β → α}
    (hf : Antitone f) (h : ∀ x, g (f x) ≥ x) (h' : ∀ y, f (g y) ≥ y) : f ∘ g ∘ f = f := by
  ext a
  apply le_antisymm
  · exact hf (h a)
  · apply h'

theorem Subtype.val_monotone {p : α → Prop} [LE α] : Monotone (Subtype.val : {x // p x} → α) :=
  fun _ _ h => h

theorem Subtype.val_strictMonotone {p : α → Prop} [LT α] : StrictMonotone (Subtype.val : {x // p x} → α) :=
  fun _ _ h => h
