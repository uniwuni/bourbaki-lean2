import BourbakiLean2.Data.Nat.Intervals

noncomputable def Nat.sum_ft (n m : Nat) (x : (i : Nat) → n ≤ i → i < m → Nat) :=
  Nat.finite_sum (fun i : Set.Ico n m => x i i.2.1 i.2.2)

noncomputable def Nat.prod_ft (n m : Nat) (x : (i : Nat) → n ≤ i → i < m → Nat) :=
  Nat.finite_prod (fun i : Set.Ico n m => x i i.2.1 i.2.2)

namespace Nat
variable {n m n' m' : Nat}

theorem Nat.sum_ft_ge {x : (i : Nat) → n ≤ i → i < m → Nat} (h : m ≤ n) : Nat.sum_ft n m x = 0 := by
  simp only [sum_ft, finite_sum_zero_iff, Subtype.forall, Set.mem_Ico_iff]
  rintro a ⟨b,c⟩
  exact (not_lt_self $ lt_of_le_lt (le_trans h b) c).elim

theorem Nat.prod_ft_ge {x : (i : Nat) → n ≤ i → i < m → Nat} (h : m ≤ n) : Nat.prod_ft n m x = 1 := by
  simp only [prod_ft]
  apply finite_prod_empty
  rintro ⟨a, ⟨b,c⟩⟩
  exact (not_lt_self $ lt_of_le_lt (le_trans h b) c).elim

@[simp] theorem Nat.sum_ft_succ_right (h : n ≤ m) {x : (i : Nat) → n ≤ i → i < m + 1 → Nat} :
    Nat.sum_ft n (m + 1) x = (Nat.sum_ft n m fun i h1 h2 => x i h1 (lt_succ_of_lt h2)) + x m h (Nat.lt_add_one m) := by
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

@[simp] theorem Nat.prod_ft_succ_right (h : n ≤ m) {x : (i : Nat) → n ≤ i → i < m + 1 → Nat} :
    Nat.prod_ft n (m + 1) x = (Nat.prod_ft n m fun i h1 h2 => x i h1 (lt_succ_of_lt h2)) * x m h (Nat.lt_add_one m) := by
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




  end Nat
