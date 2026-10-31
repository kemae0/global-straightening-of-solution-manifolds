import GlobalRegularization.MarkovApproximation
import GlobalRegularization.IntegralDensityFunctional

/-! Exact symmetry of the constructed finite positive averaging operator
under integration against its dominating measure. -/

namespace GlobalRegularization

open Set MeasureTheory

noncomputable section

variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [Fintype ι]
  [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem integral_mul_finiteMarkov_eq_sum
    (ψ : ι → C(X, ℝ)) (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1)
    (w g : C(X, ℝ)) :
    (∫ t, w t * finiteMarkovOperator ℝ μ ψ hψ hsum g t ∂μ) =
      ∑ j, ((∫ t, w t * ψ j t ∂μ) * (∫ t, ψ j t ∂μ)⁻¹) * (∫ t, ψ j t * g t ∂μ) := by
  have heq (t : X) : w t * finiteMarkovOperator ℝ μ ψ hψ hsum g t =
      ∑ j, (w t * ψ j t) * ((∫ s, ψ j s ∂μ)⁻¹ * ∫ s, ψ j s * g s ∂μ) := by
    rw [finiteMarkovOperator_apply]
    simp only [smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun j hj =>
    (integrable_density_mul_continuous μ (continuous_compact_integrable μ ℝ w) (ψ j)).mul_const _)]
  simp only [integral_mul_const]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteMarkov_self_adjoint
    (ψ : ι → C(X, ℝ)) (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1)
    (w g : C(X, ℝ)) :
    (∫ t, w t * finiteMarkovOperator ℝ μ ψ hψ hsum g t ∂μ) =
      ∫ t, finiteMarkovOperator ℝ μ ψ hψ hsum w t * g t ∂μ := by
  have heq : (fun t => finiteMarkovOperator ℝ μ ψ hψ hsum w t * g t) =
      (fun t => g t * finiteMarkovOperator ℝ μ ψ hψ hsum w t) :=
    funext (fun t => mul_comm _ _)
  rw [heq, integral_mul_finiteMarkov_eq_sum, integral_mul_finiteMarkov_eq_sum]
  have hw (j : ι) : (∫ t, w t * ψ j t ∂μ) = ∫ t, ψ j t * w t ∂μ := by
    apply integral_congr_ae
    exact ae_of_all μ (fun t => mul_comm _ _)
  have hg (j : ι) : (∫ t, g t * ψ j t ∂μ) = ∫ t, ψ j t * g t ∂μ := by
    apply integral_congr_ae
    exact ae_of_all μ (fun t => mul_comm _ _)
  simp_rw [hw, hg]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end

end GlobalRegularization
