import Mathlib.Tactic

/-!
# Triangular algebra: noncommuting nilpotent and remainder operators

These lemmas isolate finite algebraic identities used in the paper's
nilpotent-tail spectral argument. They DO NOT establish spectral-radius zero
or a global C¹ chart. The full algebraic limit argument is in TriangularLimit.
-/

namespace GlobalRegularization

section Algebra

variable {R : Type*} [Semiring R]

/-- A factor which annihilates `b` on the right also annihilates all
positive powers of `b` on the right. -/
theorem mul_pow_succ_eq_zero (a b : R) (h : a * b = 0) :
    ∀ n : ℕ, a * b ^ (n + 1) = 0 := by
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
      calc
        a * b ^ (Nat.succ n + 1) = (a * b ^ (n + 1)) * b := by
          rw [pow_succ]
          simp only [mul_assoc]
        _ = 0 := by rw [ih]; simp

/-- A direct two-step identity; this uses the **noncommutative** product
order. In particular the assumption is `a*b=0`, not `b*a=0`. -/
theorem square_add_of_annihilation (a b : R)
    (ha : a * a = 0) (hab : a * b = 0) :
    (a + b) * (a + b) = b * a + b * b := by
  calc
    (a + b) * (a + b) = a * a + a * b + (b * a + b * b) := by
      simp [add_mul, mul_add, add_assoc, add_left_comm]
    _ = b * a + b * b := by simp [ha, hab]

end Algebra

end GlobalRegularization
