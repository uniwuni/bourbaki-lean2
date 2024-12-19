import BourbakiLean2.Order.Monotone
import BourbakiLean2.Order.Lattice
import BourbakiLean2.Order.TotalOrder
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

@[simp] theorem Iio_compl [TotalOrder α] : (Iio a)ᶜ = Ici a := by
  ext x
  simp only [mem_compl_iff, mem_Iio_iff, not_gt_iff_le, mem_Ici_iff]

@[simp] theorem Ici_compl [TotalOrder α] : (Ici a)ᶜ = Iio a := by
  ext x
  simp only [mem_compl_iff, mem_Ici_iff, not_ge_iff_lt, mem_Iio_iff]

@[simp] theorem Iic_compl [TotalOrder α] : (Iic a)ᶜ = Ioi a := by
  ext x
  simp only [mem_compl_iff, mem_Iic_iff, not_ge_iff_lt, mem_Ioi_iff]

@[simp] theorem Ioi_compl [TotalOrder α] : (Ioi a)ᶜ = Iic a := by
  ext x
  simp only [mem_compl_iff, mem_Ioi_iff, not_gt_iff_le, mem_Iic_iff]

theorem iUnion_Iio_of_no_greatest [TotalOrder α] (h : ∀ a : α, ¬ Greatest a) : ⋃ a : α, Iio a = Set.univ := by
  ext b
  simp only [mem_iUnion_iff, mem_Iio_iff, mem_univ, iff_true]
  by_contra h'
  specialize h b
  rw[Greatest, Classical.not_forall] at h
  obtain ⟨x,h⟩ := h
  rw[not_ge_iff_lt] at h
  exact h' ⟨_,h⟩

theorem iUnion_Iio_of_greatest [TotalOrder α] (h : Greatest a) : ⋃ a : α, Iio a = {a}ᶜ := by
  ext b
  simp only [mem_iUnion_iff, mem_Iio_iff, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i,lt⟩ rfl
    rw[← not_ge_iff_lt] at lt
    apply lt $ h _
  · rw[imp_iff_not_imp_not, Classical.not_not]
    intro h'
    apply Greatest.all_eq
    · intro i
      rw[not_exists] at h'
      specialize h' i
      rwa[not_gt_iff_le] at h'
    · assumption

@[simp] theorem Iio_subset_Iio_iff {x y : α}  [TotalOrder α] : Set.Iio x ⊆ Set.Iio y ↔ x ≤ y := by
  constructor
  · intro h
    by_cases h' : x = y
    · rw[h']
    · rw[← not_gt_iff_le]
      intro h''
      exact not_lt_self $ h h''
  · intro h a ha
    exact lt_of_lt_le ha h

@[simp] theorem Ioi_subset_Ioi_iff {x y : α}  [TotalOrder α] : Set.Ioi x ⊆ Set.Ioi y ↔ y ≤ x := by
  constructor
  · intro h
    by_cases h' : x = y
    · rw[h']
    · rw[← not_gt_iff_le]
      intro h''
      exact not_lt_self $ h h''
  · intro h a ha
    exact lt_of_le_lt h ha

@[simp] theorem Iio_subset_Iic {x : α} [Preorder α] : Iio x ⊆ Iic x := by
  intro y
  simp only [mem_Iio_iff, mem_Iic_iff, lt_iff_le_not_le]
  exact And.left

end

/-! interval class -/
class IsInterval {α : Type*} [Preorder α] (s : Set α) where
  mem_of_mem_le_mem {a b c : α} (h : a ≤ b) (h' : b ≤ c) (ha : a ∈ s) (hc : c ∈ s) : b ∈ s

class IsDownwardsClosed {α : Type*} [Preorder α] (s : Set α) where
  mem_of_le_mem {a b : α} (h : a ≤ b) (hb : b ∈ s) : a ∈ s

class IsUpwardsClosed {α : Type*} [Preorder α] (s : Set α) where
  mem_of_mem_le {a b : α} (h : a ≤ b) (ha : a ∈ s) : b ∈ s

instance {α : Type*} [Preorder α] {s : Set α} [IsUpwardsClosed s] : IsInterval s where
  mem_of_mem_le_mem h _ ha _ := IsUpwardsClosed.mem_of_mem_le h ha

instance {α : Type*} [Preorder α] {s : Set α} [IsDownwardsClosed s] : IsInterval s where
  mem_of_mem_le_mem _ h _ hc := IsDownwardsClosed.mem_of_le_mem h hc

section
variable {α : Type*} [Preorder α] {a b c d : α}
theorem mem_of_mem_le_mem {s : Set α} [IsInterval s] (h : a ≤ b) (h' : b ≤ c) (ha : a ∈ s) (hc : c ∈ s) : b ∈ s :=
  IsInterval.mem_of_mem_le_mem h h' ha hc

theorem mem_of_le_mem {s : Set α} [IsDownwardsClosed s] {a b : α} (h : a ≤ b) (hb : b ∈ s) : a ∈ s :=
  IsDownwardsClosed.mem_of_le_mem h hb

theorem mem_of_mem_le {s : Set α} [IsUpwardsClosed s] {a b : α} (h : a ≤ b) (ha : a ∈ s) : b ∈ s :=
  IsUpwardsClosed.mem_of_mem_le h ha

instance : IsUpwardsClosed (Ici a) where
  mem_of_mem_le := fun h1 h3 => le_trans h3 h1

instance : IsDownwardsClosed (Iic a) where
  mem_of_le_mem := fun h1 h3 => le_trans h1 h3

instance : IsUpwardsClosed (Ioi a) where
  mem_of_mem_le := fun h1 h3 => by
    simp only [mem_Ioi_iff, lt_iff_le_not_le] at *
    constructor
    · apply le_trans h3.1 h1
    · intro h
      apply h3.2 $ le_trans h1 h

instance : IsDownwardsClosed (Iio a) where
  mem_of_le_mem := fun h2 h4 => by
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

instance : IsDownwardsClosed (∅ : Set α) where
  mem_of_le_mem := fun _ => nofun

instance : IsUpwardsClosed (∅ : Set α) where
  mem_of_mem_le := fun _ => nofun

instance : IsDownwardsClosed (Set.univ : Set α) where
  mem_of_le_mem := fun _ _ => True.intro

instance : IsUpwardsClosed (Set.univ : Set α) where
  mem_of_mem_le := fun _ _ => True.intro

instance {s t : Set α} [IsInterval s] [IsInterval t] : IsInterval (s ∩ t) where
  mem_of_mem_le_mem h1 h2 h3 h4 :=
    ⟨mem_of_mem_le_mem h1 h2 h3.1 h4.1, mem_of_mem_le_mem h1 h2 h3.2 h4.2⟩

instance {ι : Type*} {s : ι → Set α} [∀ i, IsInterval (s i)] : IsInterval (⋂ i, s i) where
  mem_of_mem_le_mem h1 h2 h3 h4 i := mem_of_mem_le_mem h1 h2 (h3 i) (h4 i)

instance {s t : Set α} [IsDownwardsClosed s] [IsDownwardsClosed t] : IsDownwardsClosed (s ∩ t) where
  mem_of_le_mem h1 h2 :=
    ⟨mem_of_le_mem h1 h2.1, mem_of_le_mem h1 h2.2⟩

instance {ι : Type*} {s : ι → Set α} [∀ i, IsDownwardsClosed (s i)] : IsDownwardsClosed (⋂ i, s i) where
  mem_of_le_mem h1 h2 i := mem_of_le_mem h1 $ h2 i

instance {s t : Set α} [IsUpwardsClosed s] [IsUpwardsClosed t] : IsUpwardsClosed (s ∩ t) where
  mem_of_mem_le h1 h2 :=
    ⟨mem_of_mem_le h1 h2.1, mem_of_mem_le h1 h2.2⟩

instance {ι : Type*} {s : ι → Set α} [∀ i, IsUpwardsClosed (s i)] : IsUpwardsClosed (⋂ i, s i) where
  mem_of_mem_le h1 h2 i := mem_of_mem_le h1 $ h2 i

instance {s t : Set α} [IsDownwardsClosed s] [IsDownwardsClosed t] : IsDownwardsClosed (s ∪ t) where
  mem_of_le_mem h1 h2 := by
    rcases h2 with (h|h)
    · left
      apply mem_of_le_mem h1 h
    · right
      apply mem_of_le_mem h1 h


instance IsDownwardsClosed.iUnion {ι : Type*} {s : ι → Set α} [∀ i, IsDownwardsClosed (s i)] : IsDownwardsClosed (⋃ i, s i) where
  mem_of_le_mem h1 h2 := by
    rcases h2 with ⟨i,h2⟩
    exists i
    apply mem_of_le_mem h1 h2

instance {s t : Set α} [IsUpwardsClosed s] [IsUpwardsClosed t] : IsUpwardsClosed (s ∪ t) where
  mem_of_mem_le h1 h2 := by
    rcases h2 with (h|h)
    · left
      apply mem_of_mem_le h1 h
    · right
      apply mem_of_mem_le h1 h

instance {ι : Type*} {s : ι → Set α} [∀ i, IsUpwardsClosed (s i)] : IsUpwardsClosed (⋃ i, s i) where
  mem_of_mem_le h1 h2 := by
    rcases h2 with ⟨i,h2⟩
    exists i
    apply mem_of_mem_le h1 h2

instance {s : Set α} [IsDownwardsClosed s] {t : Set s} [IsDownwardsClosed t] : IsDownwardsClosed (Subtype.val '' t : Set α) where
  mem_of_le_mem h1 h2 := by
    rw[mem_image_iff] at *
    obtain ⟨⟨a,bs⟩,rfl, bt⟩ := h2
    have as := mem_of_le_mem h1 bs
    have at2 := mem_of_le_mem (s := t) (a := ⟨_,as⟩) h1 bt
    exact ⟨_,rfl,at2⟩

instance {s : Set α} [IsUpwardsClosed s] {t : Set s} [IsUpwardsClosed t] : IsUpwardsClosed (Subtype.val '' t : Set α) where
  mem_of_mem_le h1 h2 := by
    rw[mem_image_iff] at *
    obtain ⟨⟨a,bs⟩,rfl, bt⟩ := h2
    have as := mem_of_mem_le h1 bs
    have at2 := mem_of_mem_le (s := t) (b := ⟨_,as⟩) h1 bt
    exact ⟨_,rfl,at2⟩

instance {s : Set α} [IsInterval s] {t : Set s} [IsInterval t] : IsInterval (Subtype.val '' t : Set α) where
  mem_of_mem_le_mem h1 h2 h3 h4 := by
    rw[mem_image_iff] at *
    obtain ⟨⟨b,bs⟩,rfl, bt⟩ := h3
    obtain ⟨⟨c,cs⟩,rfl, ct⟩ := h4
    have bs := mem_of_mem_le_mem h1 h2 bs cs
    have bt2 := mem_of_mem_le_mem (s := t) (b := ⟨_,bs⟩) h1 h2 bt ct
    exact ⟨_,rfl,bt2⟩

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
