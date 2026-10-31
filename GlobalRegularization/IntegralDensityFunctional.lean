import GlobalRegularization.WeightedAverages
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Integral functionals with integrable densities, their operator-norm
bounds, and approximation by continuous densities in operator norm. -/

namespace GlobalRegularization

open Set MeasureTheory Metric

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem integrable_density_mul_continuous {w : X → ℝ} (hw : Integrable w μ) (g : C(X, ℝ)) :
    Integrable (fun x => w x * g x) μ := by
  apply (hw.norm.mul_const ‖g‖).mono'
    (hw.aestronglyMeasurable.mul g.continuous.aestronglyMeasurable)
  apply ae_of_all
  intro x
  change ‖w x * g x‖ ≤ ‖w x‖ * ‖g‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm x) (norm_nonneg _)

def integralDensityL (w : X → ℝ) (hw : Integrable w μ) : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∫ x, w x * g x ∂μ
  map_add' g j := by
    simp only [ContinuousMap.add_apply, mul_add]
    exact integral_add (integrable_density_mul_continuous μ hw g) (integrable_density_mul_continuous μ hw j)
  map_smul' c g := by
    change (∫ x, w x * (c * g x) ∂μ) = c * ∫ x, w x * g x ∂μ
    simp_rw [mul_left_comm (w _) c]
    exact integral_const_mul c _

theorem norm_integralDensity_apply_le (w : X → ℝ) (hw : Integrable w μ) (g : C(X, ℝ)) :
    ‖integralDensityL μ w hw g‖ ≤ (∫ x, ‖w x‖ ∂μ) * ‖g‖ := by
  have hn := norm_integral_le_of_norm_le (f := fun x => w x * g x)
    (hw.norm.mul_const ‖g‖) (ae_of_all μ (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm x) (norm_nonneg _)))
  simpa only [integral_mul_const] using hn

def integralDensityFunctional (w : X → ℝ) (hw : Integrable w μ) : C(X, ℝ) →L[ℝ] ℝ :=
  (integralDensityL μ w hw).mkContinuous (∫ x, ‖w x‖ ∂μ) (norm_integralDensity_apply_le μ w hw)

theorem norm_integralDensityFunctional_le (w : X → ℝ) (hw : Integrable w μ) :
    ‖integralDensityFunctional μ w hw‖ ≤ ∫ x, ‖w x‖ ∂μ :=
  (integralDensityL μ w hw).mkContinuous_norm_le (integral_nonneg (fun _ => norm_nonneg _)) _

theorem integralDensityFunctional_sub
    (w v : X → ℝ) (hw : Integrable w μ) (hv : Integrable v μ) :
    integralDensityFunctional μ w hw - integralDensityFunctional μ v hv =
      integralDensityFunctional μ (fun x => w x - v x) (hw.sub hv) := by
  apply ContinuousLinearMap.ext
  intro g
  change (∫ x, w x * g x ∂μ) - (∫ x, v x * g x ∂μ) = ∫ x, (w x - v x) * g x ∂μ
  simp only [sub_mul]
  exact (integral_sub (integrable_density_mul_continuous μ hw g) (integrable_density_mul_continuous μ hv g)).symm

theorem integralDensityFunctional_mem_closure_continuous
    [T2Space X] [BorelSpace X] [μ.WeaklyRegular] (w : X → ℝ) (hw : Integrable w μ) :
    integralDensityFunctional μ w hw ∈ closure
      (range (fun v : C(X, ℝ) => integralDensityFunctional μ v (continuous_compact_integrable μ ℝ v))) := by
  apply (Metric.mem_closure_iff
    (a := integralDensityFunctional μ w hw)
    (s := range (fun v : C(X, ℝ) => integralDensityFunctional μ v (continuous_compact_integrable μ ℝ v)))).mpr
  intro ε hε
  obtain ⟨v, hv, hint⟩ := hw.exists_boundedContinuous_integral_sub_le (show 0 < ε / 2 by positivity)
  let vc : C(X, ℝ) := v.toContinuousMap
  refine ⟨integralDensityFunctional μ vc (continuous_compact_integrable μ ℝ vc), ⟨vc, rfl⟩, ?_⟩
  rw [dist_eq_norm (integralDensityFunctional μ w hw)
    (integralDensityFunctional μ vc (continuous_compact_integrable μ ℝ vc)), integralDensityFunctional_sub]
  exact (norm_integralDensityFunctional_le μ _ _).trans_lt (hv.trans_lt (by linarith))

end

end GlobalRegularization
