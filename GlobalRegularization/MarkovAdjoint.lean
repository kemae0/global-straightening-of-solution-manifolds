import GlobalRegularization.MarkovSelfAdjoint
import GlobalRegularization.SelfAdjointApproximation
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! Adjoint operator-norm approximation for all finite measures absolutely
continuous with respect to the common dominating measure. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

variable (X : Type*) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν] [ν.WeaklyRegular]

theorem markovApproximation_integralDensity_adjoint
    (hfull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < ν U)
    (w : X → ℝ) (hw : Integrable w ν) :
    Tendsto (fun n => (integralDensityFunctional ν w hw).comp
      (markovApproximation ℝ X ν n - ContinuousLinearMap.id ℝ C(X, ℝ))) atTop (𝓝 0) := by
  apply integralDensity_adjoint_tendsto ν (markovApproximation ℝ X ν)
    (norm_markovApproximation_le ℝ X ν) (markovApproximation_strong ℝ X ν hfull)
  · intro n w g
    exact finiteMarkov_self_adjoint ν _ _ _ w g

def continuousIntegralFunctional (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℝ) →L[ℝ] ℝ :=
  integralDensityFunctional μ (fun _ => 1) (integrable_const 1)

@[simp]
theorem continuousIntegralFunctional_apply (μ : Measure X) [IsFiniteMeasure μ] (g : C(X, ℝ)) :
    continuousIntegralFunctional X μ g = ∫ t, g t ∂μ := by
  change (∫ t, 1 * g t ∂μ) = _
  simp only [one_mul]

omit [ν.WeaklyRegular] in
theorem continuousIntegralFunctional_rnDeriv (μ : Measure X) [IsFiniteMeasure μ] (hac : μ ≪ ν) :
    continuousIntegralFunctional X μ = integralDensityFunctional ν
      (fun t => (μ.rnDeriv ν t).toReal) (μ.integrable_toReal_rnDeriv) := by
  apply ContinuousLinearMap.ext
  intro g
  change (∫ t, 1 * g t ∂μ) = ∫ t, (μ.rnDeriv ν t).toReal * g t ∂ν
  simp only [one_mul]
  exact (MeasureTheory.integral_rnDeriv_smul (f := fun t => g t) hac).symm

theorem markovApproximation_measure_adjoint
    (hfull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < ν U)
    (μ : Measure X) [IsFiniteMeasure μ] (hac : μ ≪ ν) :
    Tendsto (fun n => (continuousIntegralFunctional X μ).comp
      (markovApproximation ℝ X ν n - ContinuousLinearMap.id ℝ C(X, ℝ))) atTop (𝓝 0) := by
  rw [continuousIntegralFunctional_rnDeriv X ν μ hac]
  exact markovApproximation_integralDensity_adjoint X ν hfull _ _

end

end GlobalRegularization
