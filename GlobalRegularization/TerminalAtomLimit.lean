import GlobalRegularization.ShellGeometry
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The dominated-convergence endpoint-atom calculation for actual
terminal profiles and finite measures. Signed components can be represented
as differences of two finite positive measures. Riesz representation of
arbitrary functionals is a separate obligation. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

theorem terminalProfile_deriv_tendsto_indicator
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => deriv (terminalProfile (δ n) (hδ n)) t) atTop
      (𝓝 (({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) t)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [terminalProfile_deriv_zero, Set.indicator_of_mem (show (0 : ℝ) ∈ ({0} : Set ℝ) from rfl)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · have habs : 0 < |t| := abs_pos.mpr ht
    have hevent : ∀ᶠ n : ℕ in atTop, δ n / 2 < |t| := by
      filter_upwards [hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 2 * |t| by positivity))] with n hn
      linarith
    have hz : (fun n => deriv (terminalProfile (δ n) (hδ n)) t) =ᶠ[atTop] (fun _ => (0 : ℝ)) :=
      hevent.mono (fun n hn => terminalProfile_deriv_eq_zero_of_abs_gt (δ n) (hδ n) hn)
    have hnot : t ∉ ({0} : Set ℝ) := by simpa only [mem_singleton_iff] using ht
    rw [Set.indicator_of_notMem hnot]
    exact (tendsto_congr' hz).mpr tendsto_const_nhds

theorem integral_terminalProfile_deriv_tendsto_atom
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, deriv (terminalProfile (δ n) (hδ n)) t ∂μ)
      atTop (𝓝 (μ.real {0})) := by
  obtain ⟨M, hM⟩ := exists_terminalProfile_derivative_bound
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ : ℝ => M)
    (fun n => (terminalProfile_contDiff (δ n) (hδ n)).continuous_deriv_one.aestronglyMeasurable)
    (integrable_const M)
    (fun n => ae_of_all μ (fun t => hM (δ n) (hδ n) t))
    (ae_of_all μ (terminalProfile_deriv_tendsto_indicator δ hδ hlim))
  simpa only [integral_indicator_const (1 : ℝ) (measurableSet_singleton (0 : ℝ)), smul_eq_mul, mul_one] using ht

theorem integral_terminalProfile_deriv_sub_tendsto_atom
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => (∫ t, deriv (terminalProfile (δ n) (hδ n)) t ∂μ) -
      ∫ t, deriv (terminalProfile (δ n) (hδ n)) t ∂ν)
      atTop (𝓝 (μ.real {0} - ν.real {0})) :=
  (integral_terminalProfile_deriv_tendsto_atom μ δ hδ hlim).sub
    (integral_terminalProfile_deriv_tendsto_atom ν δ hδ hlim)

end

end GlobalRegularization
