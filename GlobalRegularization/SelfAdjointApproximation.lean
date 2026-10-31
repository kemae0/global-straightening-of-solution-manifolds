import GlobalRegularization.IntegralDensityFunctional
import GlobalRegularization.DenseDualApproximation

/-! Strong self-adjoint contractions on continuous functions approximate
every integral functional with an `L¹` density in operator norm. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem continuousDensity_adjoint_identity
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hsym : ∀ w g : C(X, ℝ), (∫ t, w t * P g t ∂μ) = ∫ t, P w t * g t ∂μ)
    (w : C(X, ℝ)) :
    (integralDensityFunctional μ w (continuous_compact_integrable μ ℝ w)).comp
      (P - ContinuousLinearMap.id ℝ C(X, ℝ)) =
    integralDensityFunctional μ (P w - w) (continuous_compact_integrable μ ℝ (P w - w)) := by
  apply ContinuousLinearMap.ext
  intro g
  change (∫ t, w t * (P g t - g t) ∂μ) = ∫ t, (P w t - w t) * g t ∂μ
  simp only [mul_sub, sub_mul]
  have h₁ : (∫ t, w t * P g t - w t * g t ∂μ) =
      (∫ t, w t * P g t ∂μ) - ∫ t, w t * g t ∂μ :=
    integral_sub (integrable_density_mul_continuous μ (continuous_compact_integrable μ ℝ w) (P g))
      (integrable_density_mul_continuous μ (continuous_compact_integrable μ ℝ w) g)
  have h₂ : (∫ t, P w t * g t - w t * g t ∂μ) =
      (∫ t, P w t * g t ∂μ) - ∫ t, w t * g t ∂μ :=
    integral_sub (integrable_density_mul_continuous μ (continuous_compact_integrable μ ℝ (P w)) g)
      (integrable_density_mul_continuous μ (continuous_compact_integrable μ ℝ w) g)
  rw [h₁, h₂, hsym]

theorem continuousDensity_adjoint_tendsto
    (P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hstrong : ∀ g, Tendsto (fun n => P n g) atTop (𝓝 g))
    (hsym : ∀ n (w g : C(X, ℝ)), (∫ t, w t * P n g t ∂μ) = ∫ t, P n w t * g t ∂μ)
    (w : C(X, ℝ)) :
    Tendsto (fun n => (integralDensityFunctional μ w (continuous_compact_integrable μ ℝ w)).comp
      (P n - ContinuousLinearMap.id ℝ C(X, ℝ))) atTop (𝓝 0) := by
  have hi (n : ℕ) : (∫ t, ‖P n w t - w t‖ ∂μ) ≤ ‖P n w - w‖ * μ.real univ := by
    have hb := integral_mono (continuous_compact_integrable μ ℝ (P n w - w)).norm
      (integrable_const ‖P n w - w‖) (fun t => (P n w - w).norm_coe_le_norm t)
    simpa only [integral_const, smul_eq_mul, mul_comm] using hb
  have ht : Tendsto (fun n => ‖P n w - w‖ * μ.real univ) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_mul] using
      ((hstrong w).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => w) atTop (𝓝 w))).norm.mul_const (μ.real univ)
  apply (tendsto_zero_iff_norm_tendsto_zero
    (f := fun n => (integralDensityFunctional μ w (continuous_compact_integrable μ ℝ w)).comp
      (P n - ContinuousLinearMap.id ℝ C(X, ℝ)))).mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [continuousDensity_adjoint_identity μ (P n) (hsym n) w]
  exact (norm_integralDensityFunctional_le μ _ _).trans (hi n)

theorem integralDensity_adjoint_tendsto [T2Space X] [BorelSpace X] [μ.WeaklyRegular]
    (P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ g, Tendsto (fun n => P n g) atTop (𝓝 g))
    (hsym : ∀ n (w g : C(X, ℝ)), (∫ t, w t * P n g t ∂μ) = ∫ t, P n w t * g t ∂μ)
    (w : X → ℝ) (hw : Integrable w μ) :
    Tendsto (fun n => (integralDensityFunctional μ w hw).comp
      (P n - ContinuousLinearMap.id ℝ C(X, ℝ))) atTop (𝓝 0) := by
  apply derivativeApproximation_of_mem_closure P 1 zero_le_one hP
    (range (fun v : C(X, ℝ) => integralDensityFunctional μ v (continuous_compact_integrable μ ℝ v)))
  · rintro L ⟨v, rfl⟩
    exact continuousDensity_adjoint_tendsto μ P hstrong hsym v
  · exact integralDensityFunctional_mem_closure_continuous μ w hw

end

end GlobalRegularization
