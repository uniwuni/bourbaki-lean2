import BourbakiLean2.Order.Lattice
variable {α β : Type*} {x y z : α}

class TotalOrder (α : Type*) extends PartialOrder α where
  le_total : ∀ x y : α, Comparable x y

class IsTotalOrder (r : Relation α α) extends IsPartialOrder r where
  le_total : ∀ a b, (a,b) ∈ r ∨ (b,a) ∈ r

instance {r : Relation α α} [inst : IsTotalOrder r] : TotalOrder (RelAsLE r) where
  le_total := inst.le_total

theorem TotalOrder.isTotalOrder [TotalOrder α] : IsTotalOrder ({p | p.1 ≤ p.2} : Relation α α) where
  le_antisymm := PartialOrder.le_antisymm
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans
  le_total := TotalOrder.le_total

theorem le_total [TotalOrder α] (x y : α) : x ≤ y ∨ y ≤ x := TotalOrder.le_total x y

theorem lt_trichotomy [TotalOrder α] (x y : α) : x < y ∨ x = y ∨ y < x := by
  by_cases eq : x = y
  · right; left; assumption
  · rcases le_total x y with (h'|h')
    · left
      rw[lt_iff_le_not_eq]
      solve_by_elim
    · right
      right
      rw[lt_iff_le_not_eq]
      solve_by_elim

theorem not_ge_iff_lt [TotalOrder α] : ¬ y ≤ x ↔ x < y := by
  rcases lt_trichotomy x y with (h|(h|h))
  · simp only [h, iff_true]
    intro h'
    apply not_lt_self $ lt_of_le_lt h' h
  · rw[h]
    simp only [le_rfl, not_true_eq_false, not_lt_self]
  · simp only [h, le_of_lt, not_true_eq_false, false_iff]
    intro h'
    apply not_lt_self $ lt_of_lt_lt h' h

theorem not_gt_iff_le [TotalOrder α] : ¬ y < x ↔ x ≤ y := by
  rcases le_total x y with (h|h)
  · simp only [h, iff_true]
    exact fun h' => not_lt_self $ lt_of_le_lt h h'
  · rw[← not_ge_iff_lt]
    simp only [Classical.not_not]

theorem le_of_not_ge [TotalOrder α] (h : ¬ y ≤ x) : x ≤ y := by
  rw[← not_gt_iff_le]
  simp only [lt_iff_le_not_eq, h, ne_eq, false_and, not_false_eq_true]

noncomputable instance [TotalOrder α] : Max α where
  max (x y : α) := by classical exact if x ≤ y then y else x

@[simp] theorem max_eq_left_iff [TotalOrder α] : max x y = y ↔ x ≤ y := by
  constructor
  · intro h
    simp only [max, ite_eq_left_iff] at h
    by_cases h' : x ≤ y
    · assumption
    · rw[h h']
  · intro h
    simp only [max, h, ↓reduceIte]

@[simp] theorem max_eq_right_iff [TotalOrder α] : max x y = x ↔ y ≤ x := by
  constructor
  · intro h
    simp only [max, ite_eq_right_iff] at h
    by_cases h' : y ≤ x
    · assumption
    · rw[h $ le_of_not_ge h']
  · intro h
    simp only [max, ite_eq_right_iff]
    apply le_antisymm h

noncomputable instance [TotalOrder α] : Min α where
  min (x y : α) := by classical exact if x ≤ y then x else y

@[simp] theorem min_eq_left_iff [TotalOrder α] : min x y = y ↔ y ≤ x := by
  constructor
  · intro h
    simp only [min, ite_eq_right_iff] at h
    by_cases h' : y ≤ x
    · assumption
    · rw[h $ le_of_not_ge h']
  · intro h
    simp only [min, ite_eq_right_iff]
    apply fun h' => le_antisymm h' h

@[simp] theorem min_eq_right_iff [TotalOrder α] : min x y = x ↔ x ≤ y := by
  constructor
  · intro h
    simp[min] at h
    by_cases h' : x ≤ y
    · assumption
    · rw[h h']
  · intro h
    simp only [min, ite_eq_left_iff]
    intro h'
    apply (h' h).elim

noncomputable instance [TotalOrder α] : Lattice α where
  inf := min
  sup := max
  inf_le_left := by
    intro x y
    by_cases h : x ≤ y
    · apply le_of_eq
      simpa only [min_eq_right_iff]
    · replace h := le_of_not_ge h
      have h' := h
      rw[← min_eq_left_iff] at h
      rwa[h]
  inf_le_right := by
    intro x y
    by_cases h : x ≤ y
    · simp only [min, h, ↓reduceIte, le_refl]
    · simp only [min, h, ↓reduceIte, le_refl]
  le_inf_of {x y _} h h' := by
    rcases le_total x y with (le|le)
    · rw[← min_eq_right_iff] at le
      rwa[le]
    · rw[← min_eq_left_iff] at le
      rwa[le]
  le_sup_left := by
    intro x y
    rcases le_total x y with (le|le)
    · have le' := le
      rw[← max_eq_left_iff] at le
      rwa[le]
    · rw[← max_eq_right_iff] at le
      rw[le]
  le_sup_right := by
    intro x y
    rcases le_total x y with (le|le)
    · rw[← max_eq_left_iff] at le
      rw[le]
    · have le' := le
      rw[← max_eq_right_iff] at le
      rwa[le]
  sup_le_of {x y _} h h' := by
    rcases le_total x y with (le|le)
    · rw[← max_eq_left_iff] at le
      rwa[le]
    · rw[← max_eq_right_iff] at le
      rwa[le]

instance [TotalOrder α] {p : α → Prop} : TotalOrder {x : α // p x} where
  le_total x y := le_total x.val y.val

instance [Subsingleton α] : TotalOrder α where
  le x y := True
  le_refl x := True.intro
  le_antisymm x y _ _ := Subsingleton.allEq x y
  le_trans _ _ _ _ _ := True.intro
  le_total _ _ := Or.inl True.intro

instance [TotalOrder α] : TotalOrder (Op α) where
  le_total x y := match le_total (fromOp x) (fromOp y) with
    | Or.inl a => Or.inr a
    | Or.inr a => Or.inl a

def TotalOrder.of_surjective_monotone [TotalOrder α] [PartialOrder β] {f : α → β} (h : Monotone f) (h' : f.Surjective):
    TotalOrder β where
  le_total x y := by
    obtain ⟨a,rfl⟩ := h'.exists_preimage x
    obtain ⟨b,rfl⟩ := h'.exists_preimage y
    rcases le_total a b with (h'|h')
    · left; apply h h'
    · right; apply h h'

theorem TotalOrder.inj_of_strictMono [TotalOrder α] [Preorder β] {f : α → β} (h : StrictMonotone f) : f.Injective := by
  intro x y h'
  rcases lt_trichotomy x y with (lt|(eq|gt))
  · replace lt := h lt
    rw[h'] at lt
    apply (not_lt_self lt).elim
  · exact eq
  · have lt := h gt
    rw[h'] at lt
    apply (not_lt_self lt).elim

theorem TotalOrder.inj_of_strictAnti [TotalOrder α] [Preorder β] {f : α → β} (h : StrictAntitone f) : f.Injective := by
  have: StrictMonotone (f ∘ fromOp) := by rwa[strictAnti_iff_fromOp_strictMono] at h
  have := TotalOrder.inj_of_strictMono this
  exact this

theorem TotalOrder.strictMono_reflect [TotalOrder α] [PartialOrder β] {f : α → β} (h : StrictMonotone f) : f x ≤ f y → x ≤ y := by
  rw[imp_iff_not_imp_not, not_ge_iff_lt]
  intro h'
  have := h h'
  rw[lt_iff_le_not_le] at this
  exact this.2

theorem TotalOrder.mono_lt_reflect [TotalOrder α] [PartialOrder β] {f : α → β} (h : Monotone f) : f x < f y → x < y := by
  rw[← not_ge_iff_lt]
  rw[lt_iff_le_not_eq]
  intro ⟨h1,h2⟩ h3
  exact h2 $ le_antisymm h1 $ h h3


theorem TotalOrder.strictMono_le_iff [TotalOrder α] [PartialOrder β] {f : α → β} (h : StrictMonotone f) : f x ≤ f y ↔ x ≤ y := by
  constructor
  · apply TotalOrder.strictMono_reflect h
  · apply h.monotone

theorem TotalOrder.strictMono_iso_image [TotalOrder α] [PartialOrder β] {f : α → β} (h : StrictMonotone f) (h' : f.Surjective):
    IsOrderIso f := by
  rw[isOrderIso_iff_reflect]
  constructor
  · constructor
    · apply TotalOrder.inj_of_strictMono h
    · assumption
  · constructor
    · exact h.monotone
    · intro x y h''
      rw[← not_gt_iff_le]
      intro h'''
      replace h''' := h h'''
      exact not_lt_self $ lt_of_le_lt h'' h'''

theorem isLUB_iff_ub_exists_lt [TotalOrder α] {s : Set α} : IsLUB s x ↔ (UpperBound s x ∧ ∀ y, y < x → ∃ z ∈ s, y < z) := by
  have {y : α} : (∃ z, z ∈ s ∧ y < z) ↔ ¬ UpperBound s y := by
    simp[UpperBound]
    conv =>
      arg 2
      right
      intro x
      arg 2
      rw[not_ge_iff_lt]
  conv =>
    right
    right
    intro y
    rw[this]
    rw[← not_ge_iff_lt]
    rw[← imp_iff_not_imp_not]
  rw[IsLUB]
  simp only [Least, Subtype.le_iff_val, Subtype.forall, exists_prop]

theorem isGLB_iff_lb_exists_gt [TotalOrder α] {s : Set α} : IsGLB s x ↔ (LowerBound s x ∧ ∀ y, x < y → ∃ z ∈ s, z < y) := by
  have {y : α} : (∃ z ∈ s, z < y) ↔ ¬ LowerBound s y := by
    simp[LowerBound]
    conv =>
      arg 2
      right
      intro x
      arg 2
      rw[not_ge_iff_lt]
  conv =>
    right
    right
    intro y
    rw[this]
    rw[← not_ge_iff_lt]
    rw[← imp_iff_not_imp_not]
  rw[IsGLB]
  simp only [Greatest, Subtype.le_iff_val, Subtype.forall, exists_prop]

instance [TotalOrder α] : TotalOrder (AdjoinGreatest α) where
  le_total := by
    rintro (x|a) (y|a)
    · exact le_total x y
    · left
      trivial
    · right
      trivial
    · left
      exact le_rfl

def TotalOrder.carry_bij [TotalOrder α] {β : Type*} (f : Function.Bijection α β) : TotalOrder β where
  le := (Preorder.carry_bij f).le
  le_refl := (Preorder.carry_bij f).le_refl
  le_trans := (Preorder.carry_bij f).le_trans
  le_antisymm := (PartialOrder.carry_bij f).le_antisymm
  le_total x y := le_total _ _

def IsOrderIso.totalOrder {β : Type*} [TotalOrder α] [PartialOrder β] {f : α → β} (h : IsOrderIso f) : TotalOrder β where
  le_total a b := by
    obtain ⟨a', rfl⟩ := h.bij.surj.exists_preimage a
    obtain ⟨b', rfl⟩ := h.bij.surj.exists_preimage b
    rcases le_total a' b' with (h'|h')
    · left
      exact h.monotone h'
    · right
      exact h.monotone h'
