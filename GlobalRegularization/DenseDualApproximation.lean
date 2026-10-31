import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! Uniform operator bounds extend adjoint approximation from a dense
family to its operator-norm closure. This avoids assuming any continuity
of a chosen positive/negative measure decomposition. -/

namespace GlobalRegularization

open Set Filter Metric
open scoped Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivativeApproximation_of_mem_closure
    (P : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (S : Set (E →L[ℝ] V))
    (hS : ∀ L ∈ S, Tendsto (fun n => L.comp (P n - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0))
    {L : E →L[ℝ] V} (hL : L ∈ closure S) :
    Tendsto (fun n => L.comp (P n - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ‖P n - ContinuousLinearMap.id ℝ E‖ ≤ C + 1 :=
    (norm_sub_le _ _).trans (add_le_add (hP n) (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have htol : 0 < ε / (2 * (C + 1)) := by positivity
  obtain ⟨M, hMS, hML⟩ := Metric.mem_closure_iff.mp hL (ε / (2 * (C + 1))) htol
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hS M hMS) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall : ‖M.comp (P n - ContinuousLinearMap.id ℝ E)‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN n hn
  have hdist : ‖L - M‖ < ε / (2 * (C + 1)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hML
  have hprod : ‖L - M‖ * (C + 1) < ε / 2 := by
    have ht := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hdist
    nlinarith
  rw [dist_zero_right]
  calc
    _ ≤ ‖(L - M).comp (P n - ContinuousLinearMap.id ℝ E)‖ +
        ‖M.comp (P n - ContinuousLinearMap.id ℝ E)‖ := by
      have heq : L.comp (P n - ContinuousLinearMap.id ℝ E) =
          (L - M).comp (P n - ContinuousLinearMap.id ℝ E) + M.comp (P n - ContinuousLinearMap.id ℝ E) := by
        rw [ContinuousLinearMap.sub_comp]
        abel
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ‖L - M‖ * (C + 1) + ‖M.comp (P n - ContinuousLinearMap.id ℝ E)‖ := by
      apply add_le_add_right
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _))
    _ < ε := by linarith

end GlobalRegularization
