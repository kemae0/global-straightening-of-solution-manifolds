import Mathlib.Tactic

/-!
# Noncommutative annihilation identities

These ring-theoretic statements are used when an approximation `K_N`
annihilates the remainder `R_N` on one side, `K_N * R_N = 0`.

The order is significant.  No commutativity is assumed.
The full algebraic limit argument is developed in TriangularLimit.
-/

namespace GlobalRegularization

variable {R : Type*} [Semiring R]

/-- If `a*b = 0`, then every strictly positive power of `a` annihilates `b`. -/
theorem pow_succ_mul_eq_zero (a b : R) (hab : a * b = 0) (n : ℕ) :
    a ^ (n + 1) * b = 0 := by
  calc
    a ^ (n + 1) * b = a ^ n * (a * b) := by
      rw [pow_succ, mul_assoc]
    _ = 0 := by simp [hab]

/-- If `a*b = 0`, then `a` annihilates every strictly positive power of `b`. -/
theorem mul_pow_succ_zero (a b : R) (hab : a * b = 0) (n : ℕ) :
    a * b ^ (n + 1) = 0 := by
  calc
    a * b ^ (n + 1) = (a * b) * b ^ n := by
      rw [pow_succ']
      rw [mul_assoc]
    _ = 0 := by simp [hab]

/-- The noncommutative square has only two terms if `a^2 = a*b = 0`. -/
theorem square_of_zero_and_annihilation (a b : R)
    (haa : a * a = 0) (hab : a * b = 0) :
    (a + b) * (a + b) = b * a + b * b := by
  calc
    (a + b) * (a + b) = (a * a + a * b) + (b * a + b * b) := by
      simp only [add_mul, mul_add, add_assoc, add_left_comm]
    _ = b * a + b * b := by simp [haa, hab]

end GlobalRegularization
