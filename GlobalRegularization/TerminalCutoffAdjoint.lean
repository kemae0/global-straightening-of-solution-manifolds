import GlobalRegularization.TerminalHistoryCutoff
import GlobalRegularization.HistoryFunctionalRepresentation
import GlobalRegularization.MarkovAdjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Adjoint operator-norm convergence of the terminal cutoff for a
finite measure with no endpoint atom. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section

def terminalTailBound (h : ℝ≥0) (σ : ℝ) (t : HistoryInterval h) : ℝ :=
  if -σ < (t : ℝ) then 2 else 0

theorem terminalTailBound_nonneg (h : ℝ≥0) (σ : ℝ) (t : HistoryInterval h) :
    0 ≤ terminalTailBound h σ t := by unfold terminalTailBound; split_ifs <;> norm_num

theorem terminalTailBound_integrable (h : ℝ≥0) (μ : Measure (HistoryInterval h)) [IsFiniteMeasure μ] (σ : ℝ) :
    Integrable (terminalTailBound h σ) μ := by
  apply Integrable.of_bound (C := 2)
  · apply Measurable.aestronglyMeasurable
    unfold terminalTailBound
    exact Measurable.ite (measurableSet_lt measurable_const continuous_subtype_val.measurable)
      measurable_const measurable_const
  · exact ae_of_all μ (fun t => by unfold terminalTailBound; split_ifs <;> norm_num)

theorem integral_terminalTailBound_tendsto_zero
    (h : ℝ≥0) (μ : Measure (HistoryInterval h)) [IsFiniteMeasure μ] (hμ : μ {historyRight h} = 0)
    (σ : ℕ → ℝ) (hlim : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, terminalTailBound h (σ n) t ∂μ) atTop (𝓝 0) := by
  have hne : ∀ᵐ t ∂μ, t ≠ historyRight h := by
    apply ae_iff.mpr
    simpa using hμ
  have hp : ∀ᵐ t ∂μ, Tendsto (fun n => terminalTailBound h (σ n) t) atTop (𝓝 0) := by
    filter_upwards [hne] with t ht
    have hneg : (t : ℝ) < 0 := lt_of_le_of_ne t.property.2 (fun hz => ht (Subtype.ext hz))
    have hevent : ∀ᶠ n : ℕ in atTop, σ n < -(t : ℝ) :=
      hlim.eventually (Iio_mem_nhds (neg_pos.mpr hneg))
    have hz : (fun n => terminalTailBound h (σ n) t) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [hevent] with n hn
      exact if_neg (by linarith)
    exact (tendsto_congr' hz).mpr tendsto_const_nhds
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (2 : ℝ))
    (fun n => (terminalTailBound_integrable h μ (σ n)).aestronglyMeasurable) (integrable_const 2)
    (fun n => ae_of_all μ (fun t => by unfold terminalTailBound; split_ifs <;> norm_num)) hp
  simpa only [integral_zero] using ht

theorem norm_terminalHistoryCutoff_integral_defect_le
    (h : ℝ≥0) (μ : Measure (HistoryInterval h)) [IsFiniteMeasure μ]
    (σ : ℝ) (hσh : σ ≤ (h : ℝ)) :
    ‖(continuousIntegralFunctional (HistoryInterval h) μ).comp
      (terminalHistoryCutoff h ℝ σ hσh - ContinuousLinearMap.id ℝ (ContinuousHistory h ℝ))‖ ≤
      ∫ t, terminalTailBound h σ t ∂μ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (terminalTailBound_nonneg h σ))
  intro g
  change ‖∫ t, 1 * (terminalHistoryCutoff h ℝ σ hσh g t - g t) ∂μ‖ ≤ _
  simp only [one_mul]
  have hb : Integrable (fun t => terminalTailBound h σ t * ‖g‖) μ :=
    (terminalTailBound_integrable h μ σ).mul_const ‖g‖
  have hn := norm_integral_le_of_norm_le
    (f := fun t => terminalHistoryCutoff h ℝ σ hσh g t - g t) hb (ae_of_all μ (fun t => by
      by_cases ht : (t : ℝ) ≤ -σ
      · have hp : terminalPastPoint h σ hσh t = t := by
          apply Subtype.ext
          exact min_eq_left ht
        change ‖g (terminalPastPoint h σ hσh t) - g t‖ ≤ _
        rw [hp, sub_self, norm_zero]
        exact mul_nonneg (terminalTailBound_nonneg h σ t) (norm_nonneg g)
      · have htail : terminalTailBound h σ t = 2 := if_pos (lt_of_not_ge ht)
        change ‖g (terminalPastPoint h σ hσh t) - g t‖ ≤ _
        rw [htail]
        exact (norm_sub_le _ _).trans (by linarith [g.norm_coe_le_norm (terminalPastPoint h σ hσh t), g.norm_coe_le_norm t])))
  simpa only [integral_mul_const] using hn

theorem terminalHistoryCutoff_measure_adjoint
    (h : ℝ≥0) (μ : Measure (HistoryInterval h)) [IsFiniteMeasure μ] (hμ : μ {historyRight h} = 0)
    (σ : ℕ → ℝ) (hσh : ∀ n, σ n ≤ (h : ℝ)) (hlim : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n => (continuousIntegralFunctional (HistoryInterval h) μ).comp
      (terminalHistoryCutoff h ℝ (σ n) (hσh n) - ContinuousLinearMap.id ℝ (ContinuousHistory h ℝ)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_terminalHistoryCutoff_integral_defect_le h μ (σ n) (hσh n))
    (integral_terminalTailBound_tendsto_zero h μ hμ σ hlim)

end

end GlobalRegularization
