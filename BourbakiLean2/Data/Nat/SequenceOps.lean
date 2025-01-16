import BourbakiLean2.Data.Nat.Intervals
universe u
noncomputable def Nat.sum_ft (n m : Nat) (x : (i : Nat) → Nat) :=
  Nat.finite_sum (fun i : Set.Ico n m => x i)

noncomputable def Nat.prod_ft (n m : Nat) (x : (i : Nat) → Nat) :=
  Nat.finite_prod (fun i : Set.Ico n m => x i)

namespace Nat
variable {n m n' m' : Nat}

theorem sum_ft_ge {x} (h : m ≤ n) : Nat.sum_ft n m x = 0 := by
  simp only [sum_ft, finite_sum_zero_iff, Subtype.forall, Set.mem_Ico_iff]
  rintro a ⟨b,c⟩
  exact (not_lt_self $ lt_of_le_lt (le_trans h b) c).elim

theorem prod_ft_ge {x} (h : m ≤ n) : Nat.prod_ft n m x = 1 := by
  simp only [prod_ft]
  apply finite_prod_empty
  rintro ⟨a, ⟨b,c⟩⟩
  exact (not_lt_self $ lt_of_le_lt (le_trans h b) c).elim

@[simp] theorem sum_ft_succ_right (h : n ≤ m) {x : Nat → Nat} :
    Nat.sum_ft n (m + 1) x = (Nat.sum_ft n m x) + x m := by
  simp only [sum_ft]
  rw[Nat.finite_sum_remove_one (i := ⟨m, by simp only [h, Ico_succ, Set.mem_Icc_self_right_iff_le]⟩)]
  simp only [Nat.add_right_cancel_iff]
  let this : Function.Bijection ({(⟨m, by simp only [h, Ico_succ, Set.mem_Icc_self_right_iff_le]⟩ : Set.Ico n (m + 1))} ᶜ) (Set.Ico n m) := by
    exists fun ⟨⟨a,a1,a2⟩,h⟩ => ⟨a,a1,(le_or_eq_of_le_succ a2).elim id $ False.elim ∘ h ∘ (by simp only [Set.mem_singleton_iff,
      Subtype.eq_iff, imp_self]) ∘ succ_inj'.mp⟩
    constructor
    · rintro ⟨⟨x,h1x,h2x⟩,hx⟩ ⟨⟨y,h1y,h2y⟩,hy⟩ h
      simp only [Subtype.eq_iff] at h
      simp only [h]
    · rw[Function.surj_iff]
      intro ⟨x,h1x,h2x⟩
      exists ⟨⟨x,h1x,lt_succ_of_lt h2x⟩, fun h => by simp at h; rw[h] at h2x; exact not_lt_self h2x⟩

  rw[finite_sum_reindex (f := this)]
  congr 1
  ext ⟨⟨y,h1y,h2y⟩,hy⟩
  simp only [Function.comp_apply]

@[simp] theorem prod_ft_succ_right (h : n ≤ m) {x : (i : Nat) → Nat} :
    Nat.prod_ft n (m + 1) x = (Nat.prod_ft n m x) * x m := by
  simp only [prod_ft]
  rw[Nat.finite_prod_remove_one (i := ⟨m, by simp only [h, Ico_succ, Set.mem_Icc_self_right_iff_le]⟩)]
  congr 1
  let this : Function.Bijection ({(⟨m, by simp only [h, Ico_succ, Set.mem_Icc_self_right_iff_le]⟩ : Set.Ico n (m + 1))} ᶜ) (Set.Ico n m) := by
    exists fun ⟨⟨a,a1,a2⟩,h⟩ => ⟨a,a1,(le_or_eq_of_le_succ a2).elim id $ False.elim ∘ h ∘ (by simp only [Set.mem_singleton_iff,
      Subtype.eq_iff, imp_self]) ∘ succ_inj'.mp⟩
    constructor
    · rintro ⟨⟨x,h1x,h2x⟩,hx⟩ ⟨⟨y,h1y,h2y⟩,hy⟩ h
      simp only [Subtype.eq_iff] at h
      simp only [h]
    · rw[Function.surj_iff]
      intro ⟨x,h1x,h2x⟩
      exists ⟨⟨x,h1x,lt_succ_of_lt h2x⟩, fun h => by simp at h; rw[h] at h2x; exact not_lt_self h2x⟩
  rw[finite_prod_reindex (f := this)]
  congr 1
  ext ⟨⟨y,h1y,h2y⟩,hy⟩
  simp only [Function.comp_apply]

theorem sum_ft_split {n m k} (h : n ≤ k) (h' : k ≤ m) {x} : Nat.sum_ft n m x = Nat.sum_ft n k x + Nat.sum_ft k m x := by
  induction h' with
  | refl => simp only [sum_ft, Set.mem_Ico_iff, Subtype.forall, imp_false, not_and, Nat.not_lt, imp_self,
    implies_true, finite_sum_empty, Nat.add_zero]
  | step h1 ih =>
    simp only [succ_eq_add_one]; rw[sum_ft_succ_right, sum_ft_succ_right, ih, Nat.add_assoc]
    · assumption
    · exact le_trans h h1

theorem sum_ft_le_expand_right {n m k} (h : n ≤ k) (h' : k ≤ m) {x} : Nat.sum_ft n k x ≤ Nat.sum_ft n m x := by
  rw[sum_ft_split h h']
  exact le_add_right (n.sum_ft k x) (k.sum_ft m x)

@[simp] theorem sum_ft_le_expand_one {n m} (h : n ≤ m) {x} : Nat.sum_ft n m x ≤ Nat.sum_ft n (m + 1) x :=
  sum_ft_le_expand_right h $ le_add_right _ _


theorem prod_ft_split {n m k} (h : n ≤ k) (h' : k ≤ m) {x} : Nat.prod_ft n m x = Nat.prod_ft n k x * Nat.prod_ft k m x := by
  induction h' with
  | refl => simp only [prod_ft, Set.mem_Ico_iff, Subtype.forall, imp_false, not_and, Nat.not_lt,
    imp_self, implies_true, finite_prod_empty, Nat.mul_one]
  | step h1 ih =>
    simp only [succ_eq_add_one]; rw[prod_ft_succ_right, prod_ft_succ_right, ih, Nat.mul_assoc]
    · assumption
    · exact le_trans h h1

theorem sum_ft_find_between {n m l} {x} (h : n ≤ m) (h' : l < Nat.sum_ft n m x) : ∃ k, Nat.sum_ft n k x ≤ l ∧ l < Nat.sum_ft n (k+1) x ∧ k < m := by
  obtain ⟨a,ha,lsta⟩ := WellOrder.existsLeast (s := {k | l < Nat.sum_ft n (k+1) x }) ⟨m, lt_of_lt_le h' $ sum_ft_le_expand_one h⟩
  exists a
  constructor
  swap
  · constructor
    · assumption
    · rw[← not_ge_iff_lt]
      intro h''
      have := lsta ⟨m, lt_of_lt_le h' $ sum_ft_le_expand_one h⟩
      simp only [Subtype.le_iff_val] at this
      obtain rfl := le_antisymm h'' this
      cases m with
      | zero =>
        rw[sum_ft_ge $ zero_le _] at h'
        exact not_succ_le_zero l h'
      | succ m =>
        specialize lsta ⟨m, h'⟩
        simp only [Subtype.le_iff_val] at lsta
        apply not_succ_le_self _ lsta
  · rw[← not_gt_iff_le]
    intro h'
    cases a with
    | zero =>
      rw[sum_ft_ge $ zero_le _] at h'
      exact not_succ_le_zero l h'
    | succ m =>
      specialize lsta ⟨m, h'⟩
      simp only [Subtype.le_iff_val] at lsta
      apply not_succ_le_self _ lsta

/-theorem sum_ft_le_of_le {n n' m m'} (h : n ≤ n') (h' : m' ≤ m) (h'' : n' ≤ m') {x y}
    (hxy : ∀ i (hi1 : n' ≤ i) (hi2 : i < m'), x i ≤ y i) :
    Nat.sum_ft n' m' x ≤ Nat.sum_ft n m y := by-/

theorem prod_ft_zero_iff_exists_zero {x : (i : Nat) → Nat} : Nat.prod_ft n m x = 0 ↔ ∃ i, n ≤ i ∧ i < m ∧ x i = 0 := by
  unfold prod_ft
  simp only [finite_prod_zero_iff, Subtype.exists, Set.mem_Ico_iff, exists_prop, and_assoc]

theorem prod_minus_one_even {n} : 2 ∣ n * (n - 1) := by
  induction n with
  | zero => simp only [Nat.zero_sub, Nat.mul_zero, Nat.dvd_zero]
  | succ n ih =>
    cases n with
    | zero => simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, Nat.dvd_zero]
    | succ n =>
      simp only [Nat.add_one_sub_one] at ih
      simp only [Nat.add_one_sub_one]
      rw[Nat.mul_comm, Nat.mul_add_one, Nat.mul_add_one, Nat.add_assoc, ← Nat.two_mul]
      apply Nat.dvd_add ih $ Nat.dvd_mul_right _ _

theorem sum_ft_id : Nat.sum_ft 0 n id = n * (n - 1) / 2 := by
  induction n with
  | zero => simp only [le_rfl, sum_ft_ge, Nat.zero_sub, Nat.mul_zero, Nat.zero_div]
  | succ n ih =>
    simp only [zero_le, sum_ft_succ_right, ih, id_eq, Nat.add_one_sub_one]
    conv => lhs; rhs; rw[← Nat.mul_div_cancel (n := 2) (m := n) (by simp only [zero_lt_succ])]
    symm
    rw[Nat.div_eq_of_eq_mul_left (n := 2) (by simp only [zero_lt_succ])]
    rw[Nat.add_mul (k := 2)]
    simp only [zero_lt_succ, mul_div_left]
    rw[Nat.div_mul_cancel prod_minus_one_even]
    cases n with
    | zero => simp only [Nat.zero_add, Nat.mul_zero, Nat.zero_sub, Nat.zero_mul, Nat.add_zero]
    | succ n =>
      simp only [Nat.add_one_sub_one]
      rw[← Nat.mul_add, Nat.mul_comm]
end Nat

theorem FiniteType.cardinality_disj_iUnion_ft {n m} {α : Type} [Finite α] {a : Nat → Set α} (h : Set.Disjoint (fun x : Set.Ico n m => a x.val)) :
    (Finite.ftype (⋃ i : Set.Ico n m, a i)).cardinality = Nat.sum_ft n m (fun i => (Finite.ftype (a i)).cardinality) := by
  rw[Nat.sum_ft]
  rw[← FiniteType.cardinality_disj_iUnion (a := fun i : Set.Ico n m => a i.val)]
  exact h
