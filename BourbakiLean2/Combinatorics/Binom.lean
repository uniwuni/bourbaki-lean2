import BourbakiLean2.Combinatorics.PartitionProps

theorem Nat.binom_symmetric {n k} (h : k ≤ n): binom n k = binom n (n - k) := by
  simp only [h, binom_of_le, sub_le]
  congr 1
  rw[Nat.mul_comm]
  congr
  exact Eq.symm (Nat.sub_sub_self h)

@[simp] theorem Nat.binom_self (n) : binom n n = 1 := by
  simp only [binom, le_rfl, ↓reduceIte, Nat.sub_self, factorial_zero, Nat.mul_one]
  apply Nat.div_self factorial_pos

theorem Nat.sum_binom {n} : Nat.sum_ft 0 (n+1) (binom n) = 2^n := by
  rw[← Iio_cardinality (a := n)]
  conv => lhs; rhs; intro i; rw[← Combinatorics.cardinality_subset_of_size]
  rw[← FiniteType.cardinality_sets, ← FiniteType.cardinality_disj_iUnion_ft, ← FiniteType.cardinality_univ (α := Set _)]
  · congr
    ext a
    simp only [Set.mem_iUnion_iff, Set.mem_setOf_iff, Subtype.exists, Ico_succ,
      Icc_zero, Set.mem_Iic_iff, exists_prop, exists_eq_right', FiniteType.cardinality_le_ftype_iff,
      Set.mem_univ, iff_true]
    constructor
    exact ⟨_,Subtype.val_inj⟩
  · intro i j ne
    ext a
    simp only [Set.mem_inter_iff, Set.mem_setOf_iff, Set.not_mem_empty, iff_false, not_and]
    intro h1 h2
    rw[h1] at h2
    apply ne $ Subtype.eq h2

theorem Nat.binom_succ_succ_of_le {n k} (h : k + 1 ≤ n):
    binom (n + 1) (k + 1) = binom n (k+1) + binom n k := by
  conv => rhs; rw[← Nat.Iio_cardinality (a := n)]
  rw[← Nat.Iio_cardinality (a := n + 1), ← Combinatorics.cardinality_subset_of_size, ← Combinatorics.cardinality_subset_of_size, ← Combinatorics.cardinality_subset_of_size]
  rw[← FiniteType.cardinality_disj_union]
  simp only [Finite.ftype, Set.mem_setOf_iff, Set.mem_union_iff, FiniteType.cardinality_eq_iff]
  constructor
  exists fun ⟨a,s⟩ => ⟨{x | ⟨x.val, lt_succ_of_lt x.2⟩ ∈ a}, by
    by_cases ha : ⟨n, lt_succ_self n⟩ ∈ a
    swap
    · left
      rw[← s]
      simp only [Set.mem_setOf_iff, FiniteType.cardinality_eq_iff]
      constructor
      exists fun ⟨b,hb⟩ => ⟨_,hb⟩
      constructor
      · intro ⟨x,hx⟩ ⟨y,hy⟩ h
        simp at h
        congr
        apply Subtype.eq h
      · rw[Function.surj_iff]
        intro ⟨⟨b,blt⟩,h⟩
        have : b < n := by
          rw[Set.mem_Iio_iff,Nat.lt_succ_iff_lt_or_eq] at blt
          rcases blt with (blt|blt2)
          · exact blt
          · have : ⟨b,blt⟩ = (⟨n, lt_succ_self n⟩ : Set.Iio (n+1)) := Subtype.eq blt2
            rw[this] at h
            exact (ha h).elim
        exists ⟨⟨b,this⟩, h⟩
    · right
      have : a = insert ⟨n,lt_succ_self n⟩ (a \ {⟨n,lt_succ_self n⟩}) := by
        ext ⟨i,hi⟩
        simp only [insert, Set.insert, Subtype.eq_iff, Set.mem_sdiff_iff, Set.mem_setOf_iff,
          Set.mem_singleton_iff]
        rw[or_and_left]
        constructor
        · exact fun h => ⟨Or.inr h, Classical.em _⟩
        · exact fun h => h.1.elim (fun e => e ▸ ha) id
      rw[this] at s
      change (Finite.ftype (insert ⟨n, lt_succ_self n⟩ (a \ {⟨n, lt_succ_self n⟩}) : Set _)).cardinality = k + 1 at s
      rw[FiniteType.cardinality_insert, Nat.add_one_inj] at s
      rw[← s]
      simp only [Subtype.eq_iff, FiniteType.cardinality_eq_iff]
      constructor
      exists fun ⟨⟨x,lt⟩,hx⟩ => ⟨⟨x,lt_succ_of_lt lt⟩, ⟨hx,fun h => ne_of_lt lt (Subtype.eq_iff.mp h)⟩⟩
      constructor
      · intro ⟨⟨x,ltx⟩,hx⟩ ⟨⟨y,lty⟩,hy⟩ h
        simp only at h
        congr
        injections h
      · rw[Function.surj_iff]
        intro ⟨⟨x,ltx⟩,hx,h'x⟩
        have : x < n := by
          rw[Set.mem_Iio_iff,Nat.lt_succ_iff_lt_or_eq] at ltx
          rcases ltx with (blt|blt2)
          · exact blt
          · have : ⟨x,ltx⟩ = (⟨n, lt_succ_self n⟩ : Set.Iio (n+1)) := Subtype.eq blt2
            rw[this] at h'x
            exact (h'x rfl).elim
        exists ⟨⟨_,this⟩, hx⟩
      · simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff, not_true_eq_false, and_false,
        not_false_eq_true]⟩

  constructor
  · rintro ⟨x,xn⟩ ⟨y,yn⟩ h
    simp only [Subtype.eq_iff, Set.setOf_eq_setOf_iff, Subtype.forall] at h
    congr 1
    ext ⟨i,hi⟩
    by_cases eq : i = n
    swap
    · have : i < n := by
        rw[Set.mem_Iio_iff, Nat.lt_succ_iff_lt_or_eq] at hi
        exact hi.elim id (fun h => (eq h).elim)
      exact h _ this
    · rcases eq
      have xy :(x \ {⟨n,lt_succ_self n⟩}) = (y \ {⟨n,lt_succ_self n⟩}):= by
          ext ⟨i,hi⟩
          simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff, Subtype.eq_iff, and_congr_left_iff]
          intro h2
          have : i < n := by
              rw[Set.mem_Iio_iff, Nat.lt_succ_iff_lt_or_eq] at hi
              exact hi.elim id (fun eq => (h2 eq).elim)
          apply h _ this
      by_cases hn : ⟨n, lt_succ_self _⟩ ∈ x
      · have : x = insert ⟨n,lt_succ_self n⟩ (x \ {⟨n,lt_succ_self n⟩}) := by
          ext ⟨i,hi⟩
          simp only [insert, Set.insert, Subtype.eq_iff, Set.mem_sdiff_iff, Set.mem_setOf_iff,
            Set.mem_singleton_iff]
          rw[or_and_left]
          constructor
          · exact fun h => ⟨Or.inr h, Classical.em _⟩
          · exact fun h => h.1.elim (fun e => e ▸ hn) id
        simp only [hn, true_iff]
        by_contra ny
        have xy2 : (y \ {⟨n,lt_succ_self n⟩}) = y := by
          ext i
          simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff, Subtype.eq_iff, and_iff_left_iff_imp]
          intro hi2 eq
          have : ⟨n,hi⟩ = i := Subtype.eq eq.symm
          exact ny (this ▸ hi2)
        rw[xy, xy2] at this
        rw[this] at xn
        have : y ⊆ insert ⟨n,lt_succ_self n⟩ y := fun a => Or.inr
        rw[← xn] at yn
        rw[FiniteType.eq_of_cardinality_eq_subset this yn] at ny
        simp only [insert, Set.insert, Subtype.eq_iff, Set.mem_setOf_iff, true_or,
          not_true_eq_false] at ny
      · simp only [hn, false_iff]
        intro hn'
        have : y = insert ⟨n,lt_succ_self n⟩ (y \ {⟨n,lt_succ_self n⟩}) := by
          ext ⟨i,hi⟩
          simp only [insert, Set.insert, Subtype.eq_iff, Set.mem_sdiff_iff, Set.mem_setOf_iff,
            Set.mem_singleton_iff]
          rw[or_and_left]
          constructor
          · exact fun h => ⟨Or.inr h, Classical.em _⟩
          · exact fun h => h.1.elim (fun e => e ▸ hn') id
        have xy2 : (x \ {⟨n,lt_succ_self n⟩}) = x := by
          ext i
          simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff, Subtype.eq_iff, and_iff_left_iff_imp]
          intro hi2 eq
          have : ⟨n,hi⟩ = i := Subtype.eq eq.symm
          exact hn (this ▸ hi2)
        rw[← xy, xy2] at this
        rw[this] at yn
        have : x ⊆ insert ⟨n,lt_succ_self n⟩ x := fun a => Or.inr
        rw[← yn] at xn
        rw[FiniteType.eq_of_cardinality_eq_subset this xn] at hn
        simp only [insert, Set.insert, Subtype.eq_iff, Set.mem_setOf_iff, true_or,
          not_true_eq_false] at hn
  · rw[Function.surj_iff]
    rintro ⟨s,eq⟩
    let s' := {x : Set.Iio (n+1)| ∃ h : x.val ∈ Set.Iio n, (⟨x.val, h⟩ : Set.Iio n) ∈ s}
    have : (Finite.ftype s').cardinality = (Finite.ftype s).cardinality := by
      simp only [FiniteType.cardinality_eq_iff, Finite.ftype, s']
      constructor
      apply Function.bijection_of_funcs
        (fun ⟨x,ex⟩ => ⟨⟨x.val, ex.choose⟩, ex.choose_spec⟩)
        (fun ⟨⟨x,lt⟩,hx⟩ => ⟨⟨x, lt_succ_of_lt lt⟩, ⟨lt, hx⟩⟩)
      · intro ⟨b,s⟩
        simp only
      · intro ⟨b,s⟩
        simp only
    rcases eq with (eq | eq)
    · rw[Finite.ftype, Finite.ftype, eq] at this
      exists ⟨_,this⟩
      simp only [Set.mem_setOf_iff, Subtype.eq_iff, s']
      ext ⟨i,lt⟩
      simp only [Set.mem_setOf_iff]
      exact ⟨fun h => ⟨lt,h⟩, fun ⟨h, h'⟩ => h'⟩
    · have this : (Finite.ftype (insert ⟨n, n.lt_succ_self⟩ s' : Set (Set.Iio (n+1)))).cardinality = k + 1 := by
        have : ⟨n, n.lt_succ_self⟩ ∉ s' := by
          intro hs
          simp only [Set.mem_setOf_iff, Nat.lt_irrefl, s'] at hs
          obtain ⟨h,h'⟩ := hs
          exact Set.not_mem_Iio_self h
        rw[← eq, FiniteType.cardinality_insert (h' := this)]
        congr 1



      rw[Finite.ftype] at this
      dsimp
      exists ⟨(insert ⟨n, n.lt_succ_self⟩ s'),this⟩

      simp only [Set.mem_setOf_iff, Subtype.eq_iff, s']
      ext ⟨i,lt⟩
      simp only [Set.mem_setOf_iff]
      simp only [insert, Set.insert, Subtype.eq_iff, Set.mem_setOf_iff]
      apply Iff.intro fun h => Or.inr ⟨lt,h⟩
      rintro (rfl|⟨h,h'⟩)
      · simp only [Set.not_mem_Iio_self] at lt
      · exact h'
  · ext i
    simp only [Set.mem_inter_iff, Set.mem_setOf_iff, Set.not_mem_empty, iff_false, not_and]
    intro h h'
    rw[h] at h'
    simp only [Nat.add_right_eq_self, add_one_ne_zero] at h'

@[simp low+1] theorem Nat.binom_succ_succ {n k} :
    binom (n + 1) (k + 1) = binom n (k+1) + binom n k := by
  rcases lt_trichotomy k n with (h|rfl|h)
  · exact binom_succ_succ_of_le h
  · simp only [binom_self, Nat.lt_add_one, binom_zero_of_gt, Nat.zero_add]
  · have : n < k + 1 := lt_succ_of_lt h
    simp only [Nat.add_lt_add_iff_right, h, binom_zero_of_gt, this, Nat.add_zero]

/-
theorem Nat.factorial_prod_dvd {n k : Nat} (h : k ≤ n) :  k.factorial * (n - k).factorial ∣ n.factorial := by
  induction h with
  | refl => simp only [Nat.sub_self, factorial_zero, Nat.mul_one]; exact Nat.dvd_refl _
  | step le ih =>
    unfold Dvd.dvd instDvd at *
    dsimp only at *
    obtain ⟨c,eq⟩ := ih


theorem Nat.factorial_eq_binom_mul {n k} (h : k ≤ n) : binom n k * k.factorial * (n-k).factorial = n.factorial := by
  simp only [binom_of_le h]
  rw[Nat.mul_assoc]
  rw[Nat.div_mul_cancel]
-/
