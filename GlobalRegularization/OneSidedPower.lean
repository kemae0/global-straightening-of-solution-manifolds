import GlobalRegularization.TriangularAlgebra

/-! The exact noncommutative power expansion written in the paper.
Only the one-sided annihilation `a * b = 0` is assumed. -/

namespace GlobalRegularization

variable {R : Type*} [Semiring R]

theorem one_sided_power_expansion (a b : R) (hab : a * b = 0) (k : ℕ) :
    (a + b) ^ k = ∑ j ∈ Finset.range (k + 1), b ^ (k - j) * a ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha : a * (∑ j ∈ Finset.range (k + 1), b ^ (k - j) * a ^ j) = a ^ (k + 1) := by
      rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
      have hz : (∑ j ∈ Finset.range k, a * (b ^ (k - j) * a ^ j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hpos : 0 < k - j := by have := Finset.mem_range.mp hj; omega
        obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [← mul_assoc, hq, mul_pow_succ_eq_zero a b hab q, zero_mul]
      rw [hz]
      simp only [Nat.sub_self, pow_zero, one_mul, zero_add, ← pow_succ']
    have hb : b * (∑ j ∈ Finset.range (k + 1), b ^ (k - j) * a ^ j) =
        ∑ j ∈ Finset.range (k + 1), b ^ (k + 1 - j) * a ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hle : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have he : k + 1 - j = (k - j) + 1 := by omega
      rw [← mul_assoc, ← pow_succ', he]
    rw [pow_succ', ih, add_mul, ha, hb]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, one_mul]
    exact add_comm _ _

theorem nilpotent_remainder_power_expansion (a b : R) (N k : ℕ)
    (hab : a * b = 0) (ha : a ^ (N + 2) = 0) :
    (a + b) ^ k = ∑ j ∈ Finset.range (min k (N + 1) + 1), b ^ (k - j) * a ^ j := by
  rw [one_sided_power_expansion a b hab]
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono (by omega)
  · intro j hj hnot
    have hnj : N + 2 ≤ j := by
      have := Finset.mem_range.mp hj
      have : ¬ j < min k (N + 1) + 1 := by simpa only [Finset.mem_range] using hnot
      omega
    rw [pow_eq_zero_of_le hnj ha, mul_zero]

end GlobalRegularization
