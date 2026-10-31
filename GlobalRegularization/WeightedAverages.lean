import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Normalized positive averages of actual continuous Banach-valued
functions. The zero-weight case is included, so zero partition terms do
not require an artificial positive denominator assumption. -/

namespace GlobalRegularization

open Set Filter MeasureTheory

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [NormedSpace ℝ B] [CompleteSpace B] in
theorem continuous_compact_integrable (g : C(X, B)) : Integrable g μ :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

def weightedAverageL (ψ : C(X, ℝ)) : C(X, B) →ₗ[ℝ] B where
  toFun g := (∫ x, ψ x ∂μ)⁻¹ • ∫ x, ψ x • g x ∂μ
  map_add' g j := by
    simp only [ContinuousMap.add_apply, smul_add]
    have hi : (∫ x, ψ x • g x + ψ x • j x ∂μ) =
        (∫ x, ψ x • g x ∂μ) + ∫ x, ψ x • j x ∂μ :=
      integral_add (continuous_compact_integrable μ B (ψ • g))
        (continuous_compact_integrable μ B (ψ • j))
    rw [hi, smul_add]
  map_smul' c g := by
    change (∫ x, ψ x ∂μ)⁻¹ • (∫ x, ψ x • (c • g x) ∂μ) =
      c • ((∫ x, ψ x ∂μ)⁻¹ • ∫ x, ψ x • g x ∂μ)
    have heq : (fun x => ψ x • (c • g x)) = (fun x => c • (ψ x • g x)) :=
      funext (fun x => smul_comm _ _ _)
    rw [heq, integral_smul, smul_comm]

omit [CompleteSpace B] in
theorem norm_weightedAverage_le (ψ : C(X, ℝ)) (hψ : ∀ x, 0 ≤ ψ x) (g : C(X, B)) :
    ‖weightedAverageL μ B ψ g‖ ≤ ‖g‖ := by
  have hd : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg hψ
  change ‖(∫ x, ψ x ∂μ)⁻¹ • (∫ x, ψ x • g x ∂μ)‖ ≤ _
  by_cases hz : (∫ x, ψ x ∂μ) = 0
  · rw [hz, inv_zero, zero_smul, norm_zero]
    exact norm_nonneg g
  · have hdpos : 0 < ∫ x, ψ x ∂μ := lt_of_le_of_ne hd (Ne.symm hz)
    have hi : ‖∫ x, ψ x • g x ∂μ‖ ≤ (∫ x, ψ x ∂μ) * ‖g‖ := by
      have hb : Integrable (fun x => ψ x * ‖g‖) μ :=
        (continuous_compact_integrable μ ℝ ψ).mul_const ‖g‖
      have hn := norm_integral_le_of_norm_le (f := fun x => ψ x • g x) hb (ae_of_all μ (fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ x)]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm x) (hψ x)))
      simpa only [integral_mul_const] using hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos)]
    calc
      _ ≤ (∫ x, ψ x ∂μ)⁻¹ * ((∫ x, ψ x ∂μ) * ‖g‖) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hd)
      _ = ‖g‖ := by rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

def weightedAverage (ψ : C(X, ℝ)) (hψ : ∀ x, 0 ≤ ψ x) : C(X, B) →L[ℝ] B :=
  (weightedAverageL μ B ψ).mkContinuous 1 (fun g => by
    simpa only [one_mul] using norm_weightedAverage_le μ B ψ hψ g)

omit [CompleteSpace B] in
theorem norm_weightedAverageCLM_le (ψ : C(X, ℝ)) (hψ : ∀ x, 0 ≤ ψ x) :
    ‖weightedAverage μ B ψ hψ‖ ≤ 1 :=
  (weightedAverageL μ B ψ).mkContinuous_norm_le zero_le_one _

end

end GlobalRegularization
