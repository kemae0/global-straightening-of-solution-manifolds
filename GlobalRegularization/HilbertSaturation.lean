import GlobalRegularization.HilbertBumps

/-! A bounded C¹ saturation on Hilbert-valued outputs. Its range need
not be compact. -/

namespace GlobalRegularization

open Set Metric
open scoped ContDiff

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def hilbertSaturation (r : ℝ) (v : H) : H := hilbertBump (0 : H) r v • v

theorem hilbertSaturation_contDiff (r : ℝ) : ContDiff ℝ 1 (hilbertSaturation (H := H) r) :=
  ((hilbertBump_contDiff (0 : H) r).of_le (by simp)).smul contDiff_id

theorem hilbertSaturation_norm_le (r : ℝ) (hr : 0 < r) (v : H) :
    ‖hilbertSaturation r v‖ ≤ r := by
  by_cases hz : hilbertBump (0 : H) r v = 0
  · simp only [hilbertSaturation, hz, zero_smul, norm_zero]
    exact hr.le
  · have hv := hilbertBump_support_subset (0 : H) r hr hz
    have hvn : ‖v‖ < r := by simpa only [mem_ball, dist_zero_right] using hv
    rw [hilbertSaturation, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hilbertBump_nonneg _ _ _)]
    exact (mul_le_mul_of_nonneg_right (hilbertBump_le_one _ _ _) (norm_nonneg v)).trans
      (by simpa only [one_mul] using hvn.le)

theorem hilbertSaturation_eq_self (r : ℝ) (hr : 0 < r) (v : H) (hv : ‖v‖ ≤ r / 2) :
    hilbertSaturation r v = v := by
  rw [hilbertSaturation, hilbertBump_one_of_dist_le _ r hr v (by simpa only [dist_zero_right] using hv), one_smul]

end

end GlobalRegularization
