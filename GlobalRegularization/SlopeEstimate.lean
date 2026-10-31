import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! A Banach-valued finite-difference estimate, used to compare the
Bernstein derivative coefficients with the actual derivative. -/

namespace GlobalRegularization

open Set

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem slope_error_le (u g : ℝ → B)
    (hu : ∀ t, HasDerivAt u (g t) t)
    {a b z C : ℝ} (hab : a < b)
    (hbound : ∀ t ∈ Icc a b, ‖g t - g z‖ ≤ C) :
    ‖(b - a)⁻¹ • (u b - u a) - g z‖ ≤ C := by
  let r : ℝ → B := fun t => u t - t • g z
  have hr : ∀ t ∈ Icc a b, HasDerivWithinAt r (g t - g z) (Icc a b) t := by
    intro t ht
    simpa [r] using ((hu t).sub ((hasDerivAt_id t).smul_const (g z))).hasDerivWithinAt
  have hm := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hr hbound (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  have heq : (b - a) • ((b - a)⁻¹ • (u b - u a) - g z) = r b - r a := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab.ne'), one_smul]
    simp only [r, sub_smul]
    abel
  rw [← heq] at hm
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at hm
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp (by nlinarith [hm])

end GlobalRegularization
