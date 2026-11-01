import GlobalRegularization.SumHistoryCertificates

/-! The displayed Bernstein contraction and limits in the manuscript's
sum norm, not just in an equivalent maximum norm. -/

namespace GlobalRegularization

open Filter
open scoped NNReal Topology

noncomputable section

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def sumPaperBernstein (m : ℕ) : SumC1History 1 B →L[ℝ] SumC1History 1 B :=
  (sumHistoryEquiv 1 B).symm.toContinuousLinearMap.comp
    ((paperBernstein B m).comp (sumHistoryEquiv 1 B).toContinuousLinearMap)

theorem sumPaperBernstein_commutes (m : ℕ) (x : SumC1History 1 B) :
    sumHistoryEquiv 1 B (sumPaperBernstein B m x) = paperBernstein B m (sumHistoryEquiv 1 B x) :=
  (sumHistoryEquiv 1 B).apply_symm_apply _

theorem sumPaperBernstein_contraction (m : ℕ) : ‖sumPaperBernstein B m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, sumHistory_norm, sumHistory_norm]
  change ‖historyInclusion 1 B (sumHistoryEquiv 1 B (sumPaperBernstein B m x))‖ +
    ‖historyDerivative 1 B (sumHistoryEquiv 1 B (sumPaperBernstein B m x))‖ ≤
    ‖historyInclusion 1 B (sumHistoryEquiv 1 B x)‖ + ‖historyDerivative 1 B (sumHistoryEquiv 1 B x)‖
  rw [sumPaperBernstein_commutes]
  exact add_le_add (norm_unitHistoryBernstein_value_le B (paperBernsteinIndex m) _)
    (norm_unitHistoryBernstein_derivative_le B (paperBernsteinIndex m) _)

theorem sumPaperBernstein_strong (x : SumC1History 1 B) :
    Tendsto (fun m => sumPaperBernstein B m x) atTop (𝓝 x) := by
  have ht := ((sumHistoryEquiv 1 B).symm.continuous.tendsto (sumHistoryEquiv 1 B x)).comp
    (paperBernstein_strong B (sumHistoryEquiv 1 B x))
  simpa only [sumPaperBernstein, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using ht

theorem sumPaperBernstein_continuous_operator_limit :
    Tendsto (fun m => (sumHistoryInclusion 1 B).comp (sumPaperBernstein B m) - sumHistoryInclusion 1 B)
      atTop (𝓝 0) := by
  have hc : Continuous (fun L : C1History 1 B →L[ℝ] ContinuousHistory 1 B =>
      L.comp (sumHistoryEquiv 1 B).toContinuousLinearMap) := by fun_prop
  have ht := (hc.tendsto 0).comp (paperBernstein_continuous_operator_limit B)
  have heq (m : ℕ) : ((historyInclusion 1 B).comp (paperBernstein B m) - historyInclusion 1 B).comp
      (sumHistoryEquiv 1 B).toContinuousLinearMap =
      (sumHistoryInclusion 1 B).comp (sumPaperBernstein B m) - sumHistoryInclusion 1 B := by
    ext x t
    change historyInclusion 1 B (paperBernstein B m (sumHistoryEquiv 1 B x)) t - historyInclusion 1 B (sumHistoryEquiv 1 B x) t =
      historyInclusion 1 B (sumHistoryEquiv 1 B (sumPaperBernstein B m x)) t - historyInclusion 1 B (sumHistoryEquiv 1 B x) t
    rw [sumPaperBernstein_commutes]
  simpa only [heq, ContinuousLinearMap.zero_comp] using ht

theorem sumPaperBernstein_nested (i j : ℕ) (hij : i ≤ j) (x y : SumC1History 1 B)
    (hxy : sumPaperBernstein B j x = sumPaperBernstein B j y) : sumPaperBernstein B i x = sumPaperBernstein B i y := by
  apply (sumHistoryEquiv 1 B).injective
  simp only [sumPaperBernstein_commutes] at hxy ⊢
  apply paperBernstein_nested B i j hij
  simpa only [sumPaperBernstein_commutes] using congrArg (sumHistoryEquiv 1 B) hxy

end

end GlobalRegularization
