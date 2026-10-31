import GlobalRegularization.UnitHistoryApproximation
import GlobalRegularization.BernsteinLipschitz
import GlobalRegularization.ExtendedDerivative

/-! Operator-norm convergence into continuous histories, and the resulting
derivative approximation under property (e), on the normalized interval.
This is proved uniformly on the `C¹` unit ball. -/

namespace GlobalRegularization

open Filter Set
open scoped NNReal unitInterval Topology

noncomputable section

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem unitHistoryBernstein_continuous_error_le
    (n : ℕ) (x : C1History 1 B) (δ : ℝ) (hδ : 0 < δ) :
    ‖historyInclusion 1 B (unitHistoryBernstein B n x - x)‖ ≤
      ‖historyDerivative 1 B x‖ * (δ + 1 / ((n + 1 : ℝ) * δ)) := by
  let u := unitHistoryGlobalValue B x
  let g := unitHistoryGlobalDerivative B x
  have hu : ∀ t, HasDerivAt u (g t) t := unitHistoryGlobal_hasDerivAt B x
  have hc : Continuous u := continuous_iff_continuousAt.mpr (fun t => (hu t).continuousAt)
  let f := restrictToUnitInterval u hc
  have hlip : ∀ s t : I, ‖f s - f t‖ ≤ ‖historyDerivative 1 B x‖ * |(s : ℝ) - t| := by
    intro s t
    have hm := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun a ha => (hu a).hasDerivWithinAt)
      (fun a ha => unitHistoryGlobalDerivative_bound B x a)
      (Set.mem_univ (t : ℝ)) (Set.mem_univ (s : ℝ))
    simpa only [Real.norm_eq_abs] using hm
  have hestimate := bernstein_lipschitz_error_le B f (norm_nonneg _) hlip (n + 1) (by omega) δ hδ
  have hid : f.comp unitHistoryShift = historyInclusion 1 B x := by
    ext t
    change differentiableHistoryExtension 1 B x ((t : ℝ) + 1 - 1) = _
    rw [add_sub_cancel_right]
    exact differentiableHistoryExtension_coe 1 B x t
  have hp : historyInclusion 1 B (unitHistoryBernstein B n x) =
      (bernsteinCLM B (n + 1) f).comp unitHistoryShift := by
    rw [bernsteinCLM_eq, ← bernsteinCurveSamples_eq_approximation B u hc n]
    rfl
  have hdiff : historyInclusion 1 B (unitHistoryBernstein B n x - x) =
      (bernsteinCLM B (n + 1) f - f).comp unitHistoryShift := by
    rw [map_sub, hp, ← hid]
    rfl
  rw [hdiff]
  have hprecomp : ‖(bernsteinCLM B (n + 1) f - f).comp unitHistoryShift‖ ≤
      ‖bernsteinCLM B (n + 1) f - f‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    exact (bernsteinCLM B (n + 1) f - f).norm_coe_le_norm (unitHistoryShift t)
  exact hprecomp.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hestimate)

theorem unitHistoryBernstein_operator_error_le (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ‖(historyInclusion 1 B).comp (unitHistoryBernsteinCLM B n) - historyInclusion 1 B‖ ≤
      δ + 1 / ((n + 1 : ℝ) * δ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hx := unitHistoryBernstein_continuous_error_le B n x δ hδ
  have hd : ‖historyDerivative 1 B x‖ ≤ ‖x‖ := le_max_right ‖x.val.1‖ ‖x.val.2‖
  have hfac : 0 ≤ δ + 1 / ((n + 1 : ℝ) * δ) := by positivity
  have h := hx.trans (mul_le_mul_of_nonneg_right hd hfac)
  simpa only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    mul_comm] using h

theorem unitHistoryBernstein_operator_tendsto_zero :
    Tendsto (fun n => (historyInclusion 1 B).comp (unitHistoryBernsteinCLM B n) - historyInclusion 1 B)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hw : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℝ) * (ε / 2))) atTop (𝓝 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (ε / 2)
    simpa only [zero_div, div_div] using ht
  have hevent := (tendsto_order.mp hw).2 (ε / 2) hhalf
  filter_upwards [hevent] with n hn
  rw [dist_zero_right]
  exact (unitHistoryBernstein_operator_error_le B n (ε / 2) hhalf).trans_lt (by linarith)

theorem property_e_unitHistoryBernstein_derivative_approximation
    {U : Set (C1History 1 B)} {f : C1History 1 B → B}
    (he : HasExtendedDerivative U (historyInclusion 1 B) f)
    {x : C1History 1 B} (hx : x ∈ U) :
    Tendsto (fun n => (fderiv ℝ f x).comp
      (unitHistoryBernsteinCLM B n - ContinuousLinearMap.id ℝ (C1History 1 B))) atTop (𝓝 0) := by
  apply he.tendsto_derivative_comp _ hx
  simpa only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id] using
    unitHistoryBernstein_operator_tendsto_zero B

end

end GlobalRegularization
