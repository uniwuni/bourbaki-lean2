import BourbakiLean2.Set.FiniteCardinal
universe u
namespace Nat
variable {n m n' m' : Nat}
instance preorder : Preorder Nat where
  le_refl := Nat.le_refl
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_le _ _ := Nat.lt_iff_le_not_le
instance partialOrder : PartialOrder Nat where
  le_antisymm _ _ := Nat.le_antisymm
instance totalOrder : TotalOrder Nat where
  le_total := Nat.le_total
instance WellOrder : WellOrder Nat where
  existsLeast := by
    rintro s ⟨x,ne⟩
    let t := FiniteCardinal.of_nat.{0} '' s
    have : t.Nonempty := by
      exists FiniteCardinal.of_nat x
      exact Set.val_mem_image_of_mem ne
    obtain ⟨min,mem,least⟩ := WellOrder.existsLeast this
    exists FiniteCardinal.to_nat min
    have : FiniteCardinal.to_nat min ∈ s := by
      simp only [FiniteCardinal.eq_1, Set.mem_image_iff, Subtype.eq_iff, t] at mem
      obtain ⟨y,h,h'⟩ := mem
      rw[← Subtype.eq_iff] at h
      rwa[h,FiniteCardinal.to_nat_of_nat]
    exists this
    intro ⟨y, mem⟩
    simp only [zero_eq, succ_eq_add_one,
      Subtype.le_iff_val, ge_iff_le]
    rw[← FiniteCardinal.to_nat_of_nat (n := y)]
    rw[FiniteCardinal.to_nat_le_iff]
    have : FiniteCardinal.of_nat y ∈ t :=
      Set.val_mem_image_of_mem mem
    apply least ⟨_,this⟩

theorem le_one : n ≤ 1 ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    cases n with
    | zero => exact Or.inl rfl
    | succ n' =>
      cases n' with
      | zero => exact Or.inr rfl
      | succ n'' =>
        exfalso
        simp only [reduceLeDiff] at h
  · rintro (rfl|rfl)
    · simp only [zero_le]
    · simp only [le_rfl]


theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 := by
  cases n with
  | zero => simp only [le_zero_eq, add_one_ne_zero, ne_eq, not_true_eq_false]
  | succ n => simp only [le_add_left, ne_eq, add_one_ne_zero, not_false_eq_true]

theorem le_iff_exists_eq_add : n ≤ m ↔ ∃ p, m = p + n := by
  constructor
  · intro h
    apply Nat.exists_eq_add_of_le' h
  · rintro ⟨p, rfl⟩
    apply Nat.le_add_left

theorem le_iff_exists_eq_add' : n ≤ m ↔ ∃ p, m = n + p := by
  constructor
  · intro h
    apply Nat.exists_eq_add_of_le h
  · rintro ⟨p, rfl⟩
    apply Nat.le_add_right

theorem lt_two_pow : n < 2 ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    have : 2 ^ n < 2 ^ n + 2 ^ n := by
      apply Nat.lt_add_of_pos_right
      apply Nat.pow_pos
      simp only [zero_lt_succ]
    rw[Nat.pow_add, Nat.pow_one, Nat.mul_two]
    apply lt_of_lt_le _ this
    simp only [succ_eq_add_one, Nat.add_lt_add_iff_right, ih]

theorem lt_pow_ge_lt (h : 2 ≤ n) : m < n ^ m := lt_of_lt_le lt_two_pow $ Nat.pow_le_pow_left h _


end Nat
