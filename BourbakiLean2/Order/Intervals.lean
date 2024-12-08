import BourbakiLean2.Order.Monotone
import BourbakiLean2.Order.Lattice
namespace Set
section
variable {α : Type*} [Preorder α] {a b c : α}
/-- The interval [a, ∞). -/
def Ici (a : α) : Set α := {b | a ≤ b}
/-- The interval (-∞, a]. -/
def Iic (a : α) : Set α := {b | b ≤ a}
/-- The interval (a, ∞). -/
def Ioi (a : α) : Set α := {b | a < b}
/-- The interval (∞, a). -/
def Iio (a : α) : Set α := {b | b < a}
/-- The interval (a,b) -/
def Ioo (a b : α) : Set α := {c | a < c ∧ c < b}
/-- The interval (a,b] -/
def Ioc (a b : α) : Set α := {c | a < c ∧ c ≤ b}
/-- The interval [a,b) -/
def Ico (a b : α) : Set α := {c | a ≤ c ∧ c < b}
/-- The interval [a,b] -/
def Icc (a b : α) : Set α := {c | a ≤ c ∧ c ≤ b}
/-! mem interval iff-/
@[simp] theorem mem_Ici_iff : b ∈ Ici a ↔ a ≤ b := Iff.rfl
@[simp] theorem mem_Iic_iff : b ∈ Iic a ↔ b ≤ a := Iff.rfl
@[simp] theorem mem_Ioi_iff : b ∈ Ioi a ↔ a < b := Iff.rfl
@[simp] theorem mem_Iio_iff : b ∈ Iio a ↔ b < a := Iff.rfl
@[simp] theorem mem_Ioo_iff : c ∈ Ioo a b ↔ (a < c ∧ c < b) := Iff.rfl
@[simp] theorem mem_Ioc_iff : c ∈ Ioc a b ↔ (a < c ∧ c ≤ b) := Iff.rfl
@[simp] theorem mem_Ico_iff : c ∈ Ico a b ↔ (a ≤ c ∧ c < b) := Iff.rfl
@[simp] theorem mem_Icc_iff : c ∈ Icc a b ↔ (a ≤ c ∧ c ≤ b) := Iff.rfl
/-! mem interval self -/
@[simp high] theorem mem_Ici_self : a ∈ Ici a := le_refl _
@[simp high] theorem mem_Iic_self : a ∈ Iic a := le_refl _
@[simp high] theorem not_mem_Ioi_self : a ∉ Ioi a := not_lt_self
@[simp high] theorem not_mem_Iio_self : a ∉ Iio a := not_lt_self
@[simp high] theorem not_mem_Ioo_self_left : a ∉ Ioo a b := not_lt_self ∘ And.left
@[simp high] theorem not_mem_Ioo_self_right : b ∉ Ioo a b := not_lt_self ∘ And.right
@[simp high] theorem not_mem_Ioc_self_left : a ∉ Ioc a b := not_lt_self ∘ And.left
@[simp high] theorem mem_Ioc_self_right_iff_lt : b ∈ Ioc a b ↔ a < b := by simp only [mem_Ioc_iff,
  le_rfl, and_true]
@[simp high] theorem mem_Ico_self_left_iff_lt : a ∈ Ico a b ↔ a < b := by simp only [mem_Ico_iff,
  le_refl, true_and]
@[simp high] theorem not_mem_Ico_self_right : b ∉ Ico a b := not_lt_self ∘ And.right
@[simp high] theorem mem_Icc_self_left_iff_le : a ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc_iff,
  le_refl, true_and]
@[simp high] theorem mem_Icc_self_right_iff_le : b ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc_iff,
  le_refl, and_true]
/-! intersections -/
/-- [a,∞) ∩ (-∞,b] = [a,b] -/
@[simp] theorem Ici_inter_Iic_eq_Icc : Ici a ∩ Iic b = Icc a b := by ext; rfl
/-- (a,∞] ∩ [-∞,b] = (a,b] -/
@[simp] theorem Ioi_inter_Iic_eq_Ioc : Ioi a ∩ Iic b = Ioc a b := by ext; rfl
/-- [a,∞] ∩ [-∞,b) = [a,b) -/
@[simp] theorem Ici_inter_Iio_eq_Ico : Ici a ∩ Iio b = Ico a b := by ext; rfl
/-- (a,∞] ∩ [-∞,b) = (a,b) -/
@[simp] theorem Ioi_inter_Iio_eq_Ioo : Ioi a ∩ Iio b = Ioo a b := by ext; rfl





theorem Ici_antitone : Antitone (Ici (α := α)) := fun _ _ h _ => le_trans h
theorem Ici_strictAnti : StrictAntitone (Ici (α := α)) := by
  intro a b h
  rw[lt_iff_le_not_le] at *
  apply And.intro $ Ici_antitone h.1
  intro h'
  exact h.2 $ h' mem_Ici_self

theorem Iic_monotone : Monotone (Iic (α := α)) := fun _ _ h _ h' => le_trans h' h
theorem Iic_strictMono : StrictMonotone (Iic (α := α)) := by
  intro a b h
  rw[lt_iff_le_not_le] at *
  apply And.intro $ Iic_monotone h.1
  intro h'
  exact h.2 $ h' mem_Ici_self

end
section
variable {α : Type*} [PartialOrder α] {a b c : α}
/-! empty iff -/
@[simp] theorem Icc_empty_iff_not_le : Icc a b = ∅ ↔ ¬ a ≤ b := by
  rw[Set.ext_iff]
  simp only [mem_Icc_iff, not_mem_empty, iff_false, not_and]
  constructor
  · intro h
    exact h a le_rfl
  · intro h x h' h''
    apply h $ le_trans h' h''

@[simp] theorem Ico_empty_iff_not_lt : Ico a b = ∅ ↔ ¬ a < b := by
  rw[Set.ext_iff]
  simp only [mem_Ico_iff, not_mem_empty, iff_false, not_and]
  constructor
  · intro h
    exact h a le_rfl
  · intro h x h' h''
    apply h $ lt_of_le_lt h' h''

@[simp] theorem Ioc_empty_iff_not_lt : Ioc a b = ∅ ↔ ¬ a < b := by
  rw[Set.ext_iff]
  simp only [mem_Ioc_iff, not_mem_empty, iff_false, not_and]
  constructor
  · intro h h'
    exact h b h' le_rfl
  · intro h x h' h''
    apply h $ lt_of_lt_le h' h''

@[simp] theorem Ioi_empty_iff_maximum : Ioi a = ∅ ↔ Maximal a := by
  rw[Set.ext_iff]
  simp only [mem_Ioi_iff, lt_iff_le_not_eq, ne_eq, not_mem_empty, iff_false, not_and,
    Classical.not_not, Maximal, Eq.comm]

@[simp] theorem Iio_empty_iff_minimum : Iio a = ∅ ↔ Minimal a := by
  rw[Set.ext_iff]
  simp only [mem_Iio_iff, lt_iff_le_not_eq, ne_eq, not_mem_empty, iff_false, not_and,
    Classical.not_not, Minimal]

theorem Ioi_antitone : Antitone (Ioi (α := α)) :=
  fun _ _ h _ h' => lt_of_le_lt h h'
theorem Ioi_strictAnti : StrictAntitone (Ioi (α := α)) :=
  fun a b h => by
    rw[lt_iff_le_not_eq]
    constructor
    · intro c h'
      apply lt_of_lt_lt h h'
    · intro h'
      have : b ∈ Ioi a := h
      simp only [← h', not_mem_Ioi_self] at this

theorem Iio_monotone : Monotone (Iio (α := α)) := fun _ _ h _ h' => lt_of_lt_le h' h
theorem Iio_strictAnti : StrictMonotone (Iio (α := α)) :=
  fun a b h => by
    rw[lt_iff_le_not_eq]
    constructor
    · intro c h'
      apply lt_of_lt_lt h' h
    · intro h'
      have : a ∈ Iio b := h
      simp only [← h', not_mem_Iio_self] at this

@[simp] theorem Ioi_union_point_eq_Ici : Ioi a ∪ {a} = Ici a := by
  ext b
  simp only [mem_union_iff, mem_Ioi_iff, mem_singleton_iff, Eq.comm, mem_Ici_iff, le_iff_lt_or_eq]

@[simp] theorem Iio_union_point_eq_Iic : Iio a ∪ {a} = Iic a := by
  ext b
  simp only [mem_union_iff, mem_Iio_iff, mem_singleton_iff, mem_Iic_iff, le_iff_lt_or_eq]

@[simp] theorem Ioo_union_point_eq_Ioc_of_lt (h : a < b): Ioo a b ∪ {b} = Ioc a b := by
  ext c
  simp only [mem_union_iff, mem_Ioo_iff, mem_singleton_iff, mem_Ioc_iff]
  constructor
  · rintro (⟨h,h'⟩|rfl)
    · exact ⟨h, le_of_lt h'⟩
    · exact ⟨h,le_rfl⟩
  · rw[le_iff_lt_or_eq]
    rintro ⟨h,(h'|rfl)⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr rfl

/- and so on and so on i dont need that immediately  -/

end

section
variable {α : Type*}  {a b c d : α}
/-! intersection theorems -/
@[simp] theorem Ici_inter_Ici [SupSemilattice α] : Ici a ∩ Ici b = Ici (a ⊔ b) := by
  ext c
  simp only [mem_inter_iff, mem_Ici_iff, sup_le_iff]

@[simp] theorem Ici_inter_Icc [SupSemilattice α] : Ici a ∩ Icc b c = Icc (a ⊔ b) c := by
  ext c
  simp only [mem_inter_iff, mem_Ici_iff, mem_Icc_iff, sup_le_iff, and_assoc]

@[simp] theorem Ici_inter_Ico [SupSemilattice α] : Ici a ∩ Ico b c = Ico (a ⊔ b) c := by
  ext c
  simp only [mem_inter_iff, mem_Ici_iff, mem_Ico_iff, sup_le_iff, and_assoc]

@[simp] theorem Iic_inter_Iic [InfSemilattice α] : Iic a ∩ Iic b = Iic (a ⊓ b) := by
  ext c
  simp only [mem_inter_iff, mem_Iic_iff, le_inf_iff]

@[simp] theorem Iic_inter_Ioc [InfSemilattice α] : Iic a ∩ Ioc b c = Ioc b (a ⊓ c) := by
  ext d
  simp only [mem_inter_iff, mem_Ioc_iff, mem_Iic_iff, le_inf_iff, and_left_comm]

@[simp] theorem Iic_inter_Icc [InfSemilattice α] : Iic a ∩ Icc b c = Icc b (a ⊓ c) := by
  ext d
  simp only [mem_inter_iff, mem_Iic_iff, mem_Icc_iff, le_inf_iff, and_left_comm]

@[simp] theorem Icc_inter_Icc [Lattice α] : Icc a b ∩ Icc c d = Icc (a ⊔ c) (b ⊓ d) := by
  ext e
  simp only [mem_inter_iff, mem_Icc_iff, and_left_comm, and_assoc, sup_le_iff, le_inf_iff]

@[simp] theorem Ioi_inter_Ioi_of_le [PartialOrder α] (h : a ≤ b) : Ioi a ∩ Ioi b = Ioi b := by
  ext
  simp only [mem_inter_iff, mem_Ioi_iff, and_iff_right_iff_imp]
  apply lt_of_le_lt h

@[simp] theorem Ioi_inter_Ioi_of_ge [PartialOrder α] (h : b ≤ a) : Ioi a ∩ Ioi b = Ioi a := by
  rw[inter_comm]
  simp only [h, Ioi_inter_Ioi_of_le]

@[simp] theorem Ioi_inter_Ioi_of_incomparable [SupSemilattice α] (h : Incomparable a b) : Ioi a ∩ Ioi b = Ici (a ⊔ b) := by
  ext c
  simp only [mem_inter_iff, mem_Ioi_iff, mem_Ici_iff]
  constructor
  · exact fun ⟨h, h'⟩ => sup_le_of (le_of_lt h) (le_of_lt h')
  · rw[lt_iff_le_not_le, lt_iff_le_not_le]
    simp only [sup_le_iff, and_imp]
    intro h' h''
    refine ⟨⟨h', ?_⟩, ⟨h'', ?_⟩⟩
    · exact fun le => h.2 $ le_trans h'' le
    · exact fun le => h.1 $ le_trans h' le

@[simp] theorem Iio_inter_Iio_of_le [PartialOrder α] (h : a ≤ b) : Iio a ∩ Iio b = Iio a := by
  ext
  simp only [mem_inter_iff, mem_Iio_iff, and_iff_left_iff_imp]
  exact fun h' => lt_of_lt_le h' h

@[simp] theorem Iio_inter_Iio_of_ge [PartialOrder α] (h : b ≤ a) : Iio a ∩ Iio b = Iio b := by
  ext
  simp only [mem_inter_iff, mem_Iio_iff, and_iff_right_iff_imp]
  exact fun h' => lt_of_lt_le h' h

@[simp] theorem Iio_inter_Iio_of_incomparable [InfSemilattice α] (h : Incomparable a b) : Iio a ∩ Iio b = Iic (a ⊓ b) := by
  ext c
  simp only [mem_inter_iff, mem_Iio_iff, mem_Iic_iff, le_inf_iff]
  constructor
  · exact fun ⟨h, h'⟩ => ⟨le_of_lt h, le_of_lt h'⟩
  · rw[lt_iff_le_not_le, lt_iff_le_not_le]
    simp only [sup_le_iff, and_imp]
    intro h' h''
    refine ⟨⟨h', ?_⟩, ⟨h'', ?_⟩⟩
    · exact fun le => h.1 $ le_trans le h''
    · exact fun le => h.2 $ le_trans le h'


end

/-! interval class -/
class IsInterval {α : Type*} [Preorder α] (s : Set α) where
  mem_of_mem_le_mem {a b c : α} (h : a ≤ b) (h' : b ≤ c) (ha : a ∈ s) (hc : c ∈ s) : b ∈ s


section
variable {α : Type*} [Preorder α] {a b c d : α}
theorem mem_of_mem_le_mem {s : Set α} [IsInterval s] (h : a ≤ b) (h' : b ≤ c) (ha : a ∈ s) (hc : c ∈ s) : b ∈ s :=
  IsInterval.mem_of_mem_le_mem h h' ha hc

instance : IsInterval (Ici a) where
  mem_of_mem_le_mem := fun h1 _ h3 _ => le_trans h3 h1

instance : IsInterval (Iic a) where
  mem_of_mem_le_mem := fun _ h1 _ h3 => le_trans h1 h3

instance : IsInterval (Ioi a) where
  mem_of_mem_le_mem := fun h1 h2 h3 h4 => by
    simp only [mem_Ioi_iff, lt_iff_le_not_le] at *
    constructor
    · apply le_trans h3.1 h1
    · intro h
      apply h3.2 $ le_trans h1 h

instance : IsInterval (Iio a) where
  mem_of_mem_le_mem := fun h1 h2 h3 h4 => by
    simp only [mem_Iio_iff, lt_iff_le_not_le] at *
    constructor
    · apply le_trans h2 h4.1
    · intro h
      apply h4.2 $ le_trans h h2

instance : IsInterval (Ioo a b) where
  mem_of_mem_le_mem := fun h1 h2 h3 h4 => by
    simp[lt_iff_le_not_le] at *
    constructor
    · constructor
      · apply le_trans h3.1.1 h1
      · intro h
        apply h3.1.2 $ le_trans h1 h
    · constructor
      · apply le_trans h2 h4.2.1
      · intro h
        apply h4.2.2 $ le_trans h h2

instance : IsInterval (Ioc a b) where
  mem_of_mem_le_mem := fun h1 h2 h3 h4 => by
    simp[lt_iff_le_not_le] at *
    constructor
    · constructor
      · apply le_trans h3.1.1 h1
      · intro h
        apply h3.1.2 $ le_trans h1 h
    · apply le_trans h2 h4.2

instance : IsInterval (Ico a b) where
  mem_of_mem_le_mem := fun h1 h2 h3 h4 => by
    simp[lt_iff_le_not_le] at *
    constructor
    · apply le_trans h3.1 h1
    · constructor
      · apply le_trans h2 h4.2.1
      · intro h
        apply h4.2.2 $ le_trans h h2

instance : IsInterval (Icc a b) where
  mem_of_mem_le_mem := fun h1 h2 h3 h4 => ⟨le_trans h3.1 h1, le_trans h2 h4.2⟩

instance : IsInterval (∅ : Set α) where
  mem_of_mem_le_mem := fun _ _ => nofun

instance : IsInterval (Set.univ : Set α) where
  mem_of_mem_le_mem := fun _ _ _ _ => True.intro

instance {s t : Set α} [IsInterval s] [IsInterval t] : IsInterval (s ∩ t) where
  mem_of_mem_le_mem h1 h2 h3 h4 :=
    ⟨mem_of_mem_le_mem h1 h2 h3.1 h4.1, mem_of_mem_le_mem h1 h2 h3.2 h4.2⟩

end
section
variable {α : Type*} [PartialOrder α] {a b c d : α}
instance [PartialOrder α] : IsInterval ({a} : Set α) where
  mem_of_mem_le_mem h1 h2 h3 h4 := by
    simp only [mem_singleton_iff] at *
    rw[h3] at h1
    rw[h4] at h2
    apply le_antisymm h2 h1

end
