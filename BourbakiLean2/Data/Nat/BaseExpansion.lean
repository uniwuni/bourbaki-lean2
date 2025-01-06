import BourbakiLean2.Data.Nat.Intervals
import BourbakiLean2.Order.Lex

noncomputable def Nat.base_expansion' (b k : Nat) : Lex (Set.Iio k) (fun _ => Set.Iio b) → Nat :=
  fun r => finite_sum (fun i => r i * b ^ (k - 1 - i))


theorem Nat.base_expansion'_zero {b : Nat} {x : Lex (Set.Iio 0) (fun _ => Set.Iio b)} :
    Nat.base_expansion' b 0 x = 0 := by
  let inst : Unique (Lex (Set.Iio 0) (fun _ => Set.Iio b)) := by
    constructor
    swap
    · exact ⟨fun a => (Nat.not_lt_zero _ a.property).elim⟩
    · intro f
      simp only [Lex]
      ext a
      exact (Nat.not_lt_zero _ a.property).elim
  simp only [base_expansion', Nat.zero_sub, Nat.pow_zero, Nat.mul_one, Set.mem_Iio_iff, not_lt_zero,
    Subtype.forall, imp_self, implies_true, finite_sum_empty]


theorem Nat.base_expansion'_expand_one {b k : Nat} (h' : k ≥ 1) {x : Lex (Set.Iio (k + 1)) (fun _ => Set.Iio b)} :
    Nat.base_expansion' b (k + 1) x = b * Nat.base_expansion' b k (fun ⟨a,h⟩ => x ⟨a, Nat.lt_succ_of_lt h⟩) + x ⟨k, lt_succ_self k⟩ := by
  simp only [base_expansion']
  rw[Nat.finite_sum_remove_one ⟨k, Nat.lt_succ_self k⟩]
  simp only
  rw[Nat.add_sub_cancel_right]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.add_right_cancel_iff]
  rw[← Nat.mul_finite_sum]
  conv => rhs; rhs; intro i;
          rw[← Nat.mul_left_comm, Nat.mul_comm b _]
          rhs;rhs;rw[← Nat.pow_one b]
  conv => rhs; rhs; intro i; rhs;
          rw[← Nat.pow_add, ←Nat.sub_add_comm, ←Nat.sub_add_comm, Nat.add_sub_assoc]
          simp
          · rfl
          · rfl
          · exact h'
          · exact Nat.le_sub_of_add_le i.property
  have : ∀ a, a ∈ Set.Iio (k + 1) → (a ∈ Set.Iio k ↔ a ≠ k) := by
    intro a mem
    constructor
    · intro mem2 h
      rw[h] at mem2
      simp only [Set.not_mem_Iio_self] at mem2
    · intro ne
      simp only [Iio_succ, Set.mem_Iic_iff] at mem
      apply Nat.lt_iff_le_and_ne.mpr
      exact ⟨mem,ne⟩
  conv => lhs; rhs; intro i; simp
  let f : Function.Bijection (Set.Iio k) {x : Set.Iio (k + 1) | x ∈ {⟨k, Nat.lt_succ_self _⟩} ᶜ} := by
    exists fun ⟨x,h⟩ => ⟨⟨x, lt_succ_of_lt h⟩, fun h' => not_lt_self (a := k)
      (by simp only [Set.mem_singleton_iff,
      Subtype.eq_iff] at h'; rwa[h'] at h)⟩
    constructor
    · intro ⟨x,xlt⟩ ⟨y,ylt⟩ h
      simp only [Subtype.eq_iff] at h
      congr
    · rw[Function.surj_iff]
      intro ⟨⟨b,lt⟩,ne⟩
      simp at ne
      have : b < k := by rw[lt_iff_le_not_eq]; rw[← Nat.lt_succ]; exact ⟨lt,ne⟩
      exists ⟨b,this⟩
  rw[Nat.finite_sum_reindex f]
  congr

theorem Nat.base_expansion'_expand_one_0 {b : Nat} {x : Lex (Set.Iio 1) (fun _ => Set.Iio b)} :
    Nat.base_expansion' b (0 + 1) x = b * Nat.base_expansion' b 0 (fun ⟨a,h⟩ => x ⟨a, Nat.lt_succ_of_lt h⟩) + x ⟨0, lt_succ_self 0⟩ := by
  simp only [base_expansion', reduceAdd, Nat.zero_add, Nat.sub_self, Nat.zero_sub, Nat.pow_zero,
    Nat.mul_one, Set.mem_Iio_iff, not_lt_zero, Subtype.forall, imp_self, implies_true,
    finite_sum_empty, Nat.mul_zero]
  let a : Unique (Set.Iio 1) := by
    constructor
    swap
    · exact ⟨0, Nat.one_pos⟩
    · intro ⟨b,h⟩
      simp only [default, Subtype.eq_iff]
      rwa[← lt_one_iff]
  simp only [finite_sum_unique, default]

theorem Nat.base_expansion'_expand_one_0' {b : Nat} {x : Lex (Set.Iio 1) (fun _ => Set.Iio b)} :
    Nat.base_expansion' b 1 x = b * Nat.base_expansion' b 0 (fun ⟨a,h⟩ => x ⟨a, Nat.lt_succ_of_lt h⟩) + x ⟨0, lt_succ_self 0⟩ := by
  rw[← Nat.base_expansion'_expand_one_0]


theorem Nat.base_expansion'_prop {b k : Nat} (h' : b > 1)  {x y : Lex (Set.Iio k) (fun _ => Set.Iio b)} :
  ((h : x < y) → Nat.base_expansion' b k x < Nat.base_expansion' b k y) ∧ Nat.base_expansion' b k x < b^k := by
  induction k with
  | zero =>
      simp only [base_expansion', Nat.zero_sub, Nat.pow_zero, Nat.mul_one, Set.mem_Iio_iff,
        not_lt_zero, Subtype.forall, imp_self, implies_true, finite_sum_empty, Nat.lt_irrefl,
        imp_false, Nat.lt_add_one, and_true]
      intro h'
      have : x = y := by
        unfold Lex at x y |-
        ext ⟨_,h⟩
        simp only [Set.mem_Iio_iff, not_lt_zero] at h
      rw[this] at h'
      apply not_lt_self h'
  | succ n ih =>
    cases n with
    | zero =>
      rw[Nat.base_expansion'_expand_one_0]
      simp only [reduceAdd, base_expansion'_zero, Nat.mul_zero, Nat.zero_add, Nat.pow_one]
      constructor
      swap
      · apply (x (⟨0, lt_succ_self 0⟩ : Set.Iio 1)).property
      · intro h
        rw[Nat.base_expansion'_expand_one_0']
        simp only [base_expansion'_zero, Nat.mul_zero, Nat.zero_add]
        sorry
    | succ n => sorry


theorem Nat.base_expansion_isomorphism {b k : Nat} (h : b > 1):
  ∃ f : Lex (Set.Iio k) (fun _ => Set.Iio b) → (Set.Iio (b ^ k)), IsOrderIso f := sorry
