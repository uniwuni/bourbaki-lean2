import BourbakiLean2.Combinatorics.PartitionProps

theorem Nat.binom_symmetric {n k} (h : k ≤ n): binom n k = binom n (n - k) := by
  simp only [h, binom_of_le, sub_le]
  congr 1
  rw[Nat.mul_comm]
  congr
  exact Eq.symm (Nat.sub_sub_self h)
