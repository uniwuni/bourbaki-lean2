import BourbakiLean2.Data.Nat.SequenceOps
import BourbakiLean2.Data.Nat.Intervals
namespace Nat
variable {n k : Nat}
noncomputable def factorial (n : Nat) := Nat.prod_ft 0 n (fun i => i + 1)

@[simp] theorem factorial_zero : factorial 0 = 1 := Nat.prod_ft_ge le_rfl

@[simp] theorem factorial_succ : factorial (n + 1) = factorial n * (n + 1) := by
  simp only [factorial]
  rw[Nat.prod_ft_succ_right $ zero_le _]

@[simp] theorem factorial_pos : 0 < factorial n := by
  induction n with
  | zero => simp only [factorial_zero, Nat.lt_add_one]
  | succ n ih => simp only [factorial_succ, zero_lt_succ, Nat.mul_pos_iff_of_pos_right, ih]

theorem factorial_monotone : Monotone factorial := by
  apply monotone_of_le_succ
  intro h
  simp only [factorial_succ]
  exact Nat.le_mul_of_pos_right h.factorial $ zero_lt_succ _

theorem factorial_lt_succ : factorial (n + 1) < factorial ((n + 1) + 1) := by
  simp only [factorial_succ]
  refine Nat.mul_lt_mul_of_le_of_lt' ?hac (by simp only [Nat.lt_add_one]) (by simp only [factorial_pos])
  refine Nat.le_mul_of_pos_right n.factorial $ zero_lt_succ _

theorem factorial_strictMono : StrictMonotone (fun n => factorial (n + 1)) := by
  apply strictMono_of_lt_succ
  apply factorial_lt_succ

noncomputable def binom (n k : Nat) := if k ≤ n then n.factorial / (k.factorial * (n - k).factorial) else 0

@[simp] theorem binom_zero_of_gt : n < k → binom n k = 0 := by
  intro h
  rw[← not_ge_iff_lt] at h
  simp only [binom, ite_eq_right_iff]
  intro h'
  exact (h h').elim

@[simp low] theorem binom_of_le : k ≤ n → binom n k = n.factorial / (k.factorial * (n - k).factorial) := by
  intro h
  simp only [binom, h, ↓reduceIte]


end Nat
