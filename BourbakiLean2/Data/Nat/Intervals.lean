import BourbakiLean2.Data.Nat.IndexedOps
import BourbakiLean2.Order.Finite
variable {a b c d : Nat}

@[simp] theorem Nat.Icc_zero : Set.Icc 0 b = Set.Iic b := by
  ext i
  simp only [Set.mem_Icc_iff, zero_le, true_and, Set.mem_Iic_iff]

@[simp] theorem Nat.Ico_zero : Set.Ico 0 b = Set.Iio b := by
  ext i
  simp only [Set.mem_Ico_iff, zero_le, true_and, Set.mem_Iio_iff]

@[simp] theorem Nat.Ici_zero : Set.Ici 0 = Set.univ := by
  ext i
  simp only [Set.mem_Ici_iff, zero_le, Set.mem_univ]
namespace Nat
@[simp] def shift (c : Nat) : Set.Icc a b → Set.Icc (a + c) (b + c) :=
  fun ⟨x,h⟩ => ⟨x+c, ⟨Nat.add_le_add_right h.1 c, Nat.add_le_add_right h.2 c⟩⟩

theorem shift_isOrderIso : IsOrderIso (shift (a := a) (b := b) c) := by
  apply isOrderIso_iff_reflect.mpr
  constructor
  · constructor
    · intro x y h
      simp only [shift, Subtype.eq_iff, Nat.add_right_cancel_iff] at h
      exact Subtype.eq h
    · rw[Function.surj_iff]
      intro ⟨d,h1,h2⟩
      rw[Nat.le_iff_exists_eq_add] at h1
      obtain ⟨p,rfl⟩ := h1
      rw[← Nat.add_assoc] at h1 h2
      rw[Nat.add_le_add_iff_right] at h1 h2
      exists ⟨p + a, h1, h2⟩
      simp only [shift, Nat.add_assoc]
  · constructor
    · intro ⟨x,hx1,hx2⟩ ⟨y,hy1,hy2⟩ h
      simp only [Subtype.le_iff_val] at h
      simp only [shift, Subtype.le_iff_val, Nat.add_le_add_iff_right, h]
    · intro ⟨x,hx1,hx2⟩ ⟨y,hy1,hy2⟩ h
      simp only [shift, Subtype.le_iff_val, Nat.add_le_add_iff_right] at h
      exact h

@[simp] def unshift (c : Nat) : Set.Icc (a + c) (b + c) → Set.Icc a b :=
  fun ⟨x,h⟩ => ⟨x-c, ⟨Nat.le_sub_of_add_le h.1, Nat.sub_le_of_le_add h.2⟩⟩

theorem shift_inverse_unshift : (shift c (a := a) (b := b)).IsInverseOf (unshift c) := by
  constructor
  · ext a
    rcases a with ⟨a,h,h'⟩
    simp only [Function.comp_apply, shift, unshift, id_eq]
    rw[Nat.sub_add_cancel]
    apply Nat.le_of_add_right_le
    rw[Nat.add_comm] at h
    assumption
  · ext a
    rcases a with ⟨a,h,h'⟩
    simp only [Function.comp_apply, shift, unshift, id_eq]
    rw[Nat.add_sub_cancel]

theorem unshift_isOrderIso : IsOrderIso (unshift (a := a) (b := b) c) := by
  suffices unshift (a := a) (b := b) c = shift_isOrderIso.bij.inv by
    rw[this]
    apply shift_isOrderIso.inv
  symm
  apply shift_inverse_unshift.eq_inv


@[simp] theorem shift_unshift_val {d} : unshift c (shift c (a := a) (b := b) d) = d :=
  shift_inverse_unshift.gf_eq

@[simp] theorem unshift_shift_val {d} : shift c (unshift c (a := a) (b := b) d) = d :=
  shift_inverse_unshift.fg_eq

@[simp] theorem shift_zero : shift 0 (a := a) (b := b) = id := by
  ext x
  simp only [Nat.add_zero, shift, id_eq]

@[simp] theorem unshift_zero : unshift 0 (a := a) (b := b) = id := by
  ext x
  simp only [unshift, Nat.add_zero, Nat.sub_zero, id_eq]

instance Iic_finite : Finite (Set.Iic a) := by
  induction a with
  | zero => simp only [Set.mem_Iic_iff, le_zero_eq]
            change Finite ({0} : Set Nat)
            infer_instance
  | succ n ih =>
    unfold Set.Iic
    conv => rhs; rhs; intro a; lhs; intro b; lhs; intro b; rw[le_iff_lt_or_eq]; rw[lt_succ]
    change Finite ((Set.Iic n ∪ {n+1}) : Set Nat)
    infer_instance

instance Icc_finite : Finite (Set.Icc a b) := by
  rcases le_total a b with (h|h)
  · rw[le_iff_exists_eq_add'] at h
    obtain ⟨p,rfl⟩ := h
    conv => rhs; rhs; intro b; lhs; lhs; rw[← Nat.add_zero (n := a)]
    rw[Nat.add_comm (m := 0), Nat.add_comm (m := p)]
    apply Finite.of_bij_finite (h := ?asd) ⟨_,(shift_isOrderIso (c := a)).bij⟩
    simp only [Icc_zero]
    infer_instance
  · rw[le_iff_lt_or_eq] at h
    rcases h with (h|rfl)
    · rw[← not_ge_iff_lt, ← Set.Icc_empty_iff_not_le] at h
      rw[h]
      infer_instance
    · simp only [Set.Icc_self]
      infer_instance

@[simp] theorem Iio_succ : Set.Iio (a + 1) = Set.Iic a := by
  ext b
  simp only [Set.mem_Iio_iff, Set.mem_Iic_iff]
  apply lt_succ

@[simp] theorem Ioi_eq_Ici_succ : Set.Ioi a = Set.Ici (a + 1) := by
  ext b
  simp only [Set.mem_Ioi_iff, Set.mem_Ici_iff, succ_le]

@[simp] theorem Ioo_eq_Ico_succ : Set.Ioo a b = Set.Ico (a + 1) b := by
  ext b
  simp only [Set.mem_Ioo_iff, Set.mem_Ico_iff, succ_le]

@[simp] theorem Ico_succ : Set.Ico a (b + 1) = Set.Icc a b := by
  ext b
  simp only [Set.mem_Ico_iff, lt_succ, Set.mem_Icc_iff]

@[simp] theorem Ioc_eq_Icc_succ : Set.Ioc a b = Set.Icc (a + 1) b := by
  ext b
  simp only [Set.mem_Ioc_iff, Set.mem_Icc_iff, succ_le]

instance Iio_finite : Finite (Set.Iio a) := by
  cases a
  · simp only [Set.mem_Iio_iff, not_lt_zero]
    change Finite (∅ : Set Nat)
    infer_instance
  · simp only [Iio_succ]; infer_instance

instance Ico_finite : Finite (Set.Ico a b) := by
  cases b
  · simp only [Set.mem_Ico_iff, not_lt_zero, and_false]
    change Finite (∅ : Set Nat)
    infer_instance
  · simp only [Ico_succ]; infer_instance

instance Ioo_finite : Finite (Set.Ioo a b) := by
  cases b
  · simp only [Ioo_eq_Ico_succ, Set.mem_Ico_iff, not_lt_zero, and_false]
    change Finite (∅ : Set Nat)
    infer_instance
  · simp only [Ioo_eq_Ico_succ, Ico_succ]; infer_instance

instance Ioc_finite : Finite (Set.Ioc a b) := by
  simp only [Ioc_eq_Icc_succ]; infer_instance

@[simp] theorem Iic_cardinality : (Finite.ftype $ Set.Iic a).cardinality = a + 1 := by
  induction a with
  | zero =>
    simp only [Set.mem_Iic_iff, le_zero_eq, Nat.zero_add];
    change (Finite.ftype ({0} : Set _)).cardinality = 1
    apply FiniteType.cardinality_singleton
  | succ n ih =>
    have : Set.Iic (n + 1) = {n+1} ∪ Set.Iic n := by
      ext a
      simp only [Set.mem_Iic_iff, Set.mem_union_iff, Set.mem_singleton_iff]
      rw[le_iff_lt_or_eq (a := a) (b := n+1),Or.comm]
      apply or_congr_right
      exact Nat.lt_add_one_iff
    simp only [this]
    rw[FiniteType.cardinality_manual_insert, ih]
    · simp only [Set.mem_Iic_iff, Nat.not_le, Nat.lt_add_one]

@[simp] theorem Iio_cardinality : (Finite.ftype $ Set.Iio a).cardinality = a := by
  cases a
  · simp only [Set.mem_Iio_iff, not_lt_zero]
    change (Finite.ftype (∅ : Set Nat)).cardinality = 0
    exact FiniteType.cardinality_empty_set
  · simp only [Iio_succ, Iic_cardinality]

@[simp] theorem Icc_cardinality (h : a ≤ b): (Finite.ftype $ Set.Icc a b).cardinality = b - a + 1 := by
  rw[le_iff_exists_eq_add'] at h
  obtain ⟨p,rfl⟩ := h
  conv => lhs; rhs; rhs; rhs; intro _a; lhs; lhs; rw[← Nat.add_zero (n := a)]
  conv => lhs; rhs; rhs; rhs; intro _a; lhs; rw[Nat.add_comm (m := 0), Nat.add_comm (m := p)]
  rw[Nat.add_sub_cancel_left]
  rw[← Iic_cardinality]
  apply FiniteType.cardinality_eq_iff.mpr
  constructor
  simp only [Finite.ftype]
  rw[← Icc_zero]
  exact ⟨_,unshift_isOrderIso.bij⟩

@[simp] theorem Ioc_cardinality : (Finite.ftype $ Set.Ioc a b).cardinality = b - a := by
  by_cases h : a < b
  · simp only [Ioc_eq_Icc_succ]
    rw[Icc_cardinality]
    rw[← Nat.sub_sub, Nat.sub_add_cancel]
    rw[Nat.le_sub_iff_add_le]
    · rw[← succ_le] at h
      rwa[one_add]
    · apply le_of_lt h
    · rwa[← succ_le] at h
  · rw[not_gt_iff_le, le_iff_lt_or_eq] at h
    rcases h with (h|rfl)
    · have := (Set.Ioc_empty_iff_not_lt (a := a) (b := b)).mpr (fun h' => not_lt_self $ lt_of_lt_lt h h')
      simp only [this, Nat.sub_self]
      rw[Nat.sub_eq_zero_of_le $ le_of_lt h]
      exact FiniteType.cardinality_empty_set
    · have := (Set.Ioc_empty_iff_not_lt (a := b) (b := b)).mpr not_lt_self
      simp only [this, Nat.sub_self]
      exact FiniteType.cardinality_empty_set

@[simp] theorem Ico_cardinality : (Finite.ftype $ Set.Ico a b).cardinality = b - a := by
  rcases b with (_|n)
  · simp only [Set.mem_Ico_iff, not_lt_zero, and_false, Nat.zero_sub]
    change (Finite.ftype (∅ : Set Nat)).cardinality = 0
    exact FiniteType.cardinality_empty_set
  · simp only [Ico_succ]
    by_cases h : a ≤ n
    · rw[Icc_cardinality h, Nat.sub_add_comm h]
    · simp[Set.Icc_empty_iff_not_le.mpr h]
      change (Finite.ftype (∅ : Set Nat)).cardinality = n + 1 - a
      rw [@FiniteType.cardinality_empty_set]
      symm
      rw[Nat.sub_eq_zero_iff_le]
      rw[Nat.not_le] at h
      rwa[succ_le]

@[simp] theorem Ioo_cardinality : (Finite.ftype $ Set.Ioo a b).cardinality = b - a - 1 := by
  rcases b with (_|n)
  · simp only [Set.mem_Ioo_iff, not_lt_zero, and_false, Nat.zero_sub]
    change (Finite.ftype (∅ : Set Nat)).cardinality = 0
    exact FiniteType.cardinality_empty_set
  · simp only [Ioo_eq_Ico_succ]
    rw[Ico_cardinality]
    rfl

end Nat

theorem Finite.equipotent_Iio {α : Type*} [Finite α] : Equipotent α $ Set.Iio (Finite.ftype α).cardinality := by
  apply FiniteCardinal.equipotent_of_nat_eq (n := (Finite.ftype α).cardinality)
  · simp only [FiniteType.cardinality, FiniteType.cardinality', Finite.ftype,
    FiniteCardinal.of_nat_to_nat]
  · have : Cardinal.Finite (Cardinal.mk { a // a ∈ Set.Iio (Finite.ftype α).cardinality }) := Finite.finite
    change (⟨Cardinal.mk { a // a ∈ Set.Iio (Finite.ftype α).cardinality }, this⟩ : FiniteCardinal).val = (FiniteCardinal.of_nat (Finite.ftype α).cardinality).val
    apply Subtype.eq_iff.mp
    apply FiniteCardinal.to_nat_bij.inj
    rw[← FiniteType.cardinality']
    rw[← FiniteType.cardinality]
    simp only [FiniteCardinal.to_nat_of_nat]
    apply Nat.Iio_cardinality


theorem TotalOrder.iso_interval {α : Type*} [TotalOrder α] [Finite α] :
    ∃ f : α → Set.Iio (Finite.ftype α).cardinality, IsOrderIso f := by
  have := WellOrder.either_embeds α $ Set.Iio (Finite.ftype α).cardinality
  rcases this with (⟨seg,f,iso⟩|⟨seg,f,iso⟩)
  · have : seg.val = Set.univ := by
      by_contra h'
      have lt := Finite.ssubset_cardinal_lt h'
      have equi1: Equipotent _ _ := ⟨(⟨f,iso.bij⟩ : Function.Bijection _ _)⟩
      have equi2 : Equipotent α $ Set.Iio (Finite.ftype α).cardinality :=
        Finite.equipotent_Iio
      have := Cardinal.eq_iff.mpr $ equi1.symm.trans equi2
      rw[this] at lt
      apply (not_lt_self lt).elim
    have isuniv : seg = WellOrder.InitialSegment.univ := by
      unfold WellOrder.InitialSegment.univ
      apply Subtype.eq this
    exists Subtype.val ∘ f
    apply isOrderIso_iff_reflect.mpr
    constructor
    · constructor
      · apply Function.Injective.comp
        · exact Subtype.val_inj
        · exact iso.bij.inj
      · apply Function.Surjective.comp
        · rw[Function.Surjective, Subtype.val_image, this]
        · exact iso.bij.surj
    · constructor
      · intro x y h
        apply iso.monotone h
      · intro x y h
        apply iso.le_iff.mp h
  · have : seg.val = Set.univ := by
      by_contra h'
      have lt := Finite.ssubset_cardinal_lt h'
      have equi1: Equipotent _ _ := ⟨(⟨f,iso.bij⟩ : Function.Bijection _ _)⟩
      have equi2 : Equipotent α $ Set.Iio (Finite.ftype α).cardinality :=
        Finite.equipotent_Iio
      have := Cardinal.eq_iff.mpr $ equi1.trans equi2.symm
      rw[this] at lt
      apply (not_lt_self lt).elim
    have isuniv : seg = WellOrder.InitialSegment.univ := by
      unfold WellOrder.InitialSegment.univ
      apply Subtype.eq this
    have : ∀ x, x ∈ seg.val := by intro x; rw[this]; trivial
    exists f ∘ (fun x => ⟨x, this x⟩)
    apply isOrderIso_iff_reflect.mpr
    constructor
    · constructor
      · apply Function.Injective.comp
        · exact iso.bij.inj
        · intro x y h
          rwa [Subtype.eq_iff] at h
      · apply Function.Surjective.comp
        · exact iso.bij.surj
        · rw[Function.surj_iff]
          intro ⟨b,h⟩
          exists b
    · constructor
      · intro x y h
        apply iso.monotone h
      · intro x y h
        apply iso.le_iff.mp h
