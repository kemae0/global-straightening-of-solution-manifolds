import GlobalRegularization.WeightedAverages

/-! Local oscillation estimates for normalized positive averages. The
estimate only uses values on the support of the averaging weight. -/

namespace GlobalRegularization

open Set MeasureTheory

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem weightedAverage_const (ψ : C(X, ℝ)) (hψ : ∀ x, 0 ≤ ψ x)
    (hd : (∫ x, ψ x ∂μ) ≠ 0) (v : B) :
    weightedAverage μ B ψ hψ (ContinuousMap.const X v) = v := by
  change (∫ x, ψ x ∂μ)⁻¹ • (∫ x, ψ x • v ∂μ) = v
  rw [integral_smul_const, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem weightedAverage_sub_const_le (ψ : C(X, ℝ)) (hψ : ∀ x, 0 ≤ ψ x)
    (hd : 0 < ∫ x, ψ x ∂μ) (g : C(X, B)) (v : B) (η : ℝ)
    (hosc : ∀ x, ψ x ≠ 0 → ‖g x - v‖ ≤ η) :
    ‖weightedAverage μ B ψ hψ g - v‖ ≤ η := by
  have heq : weightedAverage μ B ψ hψ g - v =
      weightedAverage μ B ψ hψ (g - ContinuousMap.const X v) := by
    rw [map_sub, weightedAverage_const μ B ψ hψ hd.ne']
  rw [heq]
  change ‖(∫ x, ψ x ∂μ)⁻¹ • (∫ x, ψ x • (g x - v) ∂μ)‖ ≤ η
  have hb : Integrable (fun x => ψ x * η) μ :=
    (continuous_compact_integrable μ ℝ ψ).mul_const η
  have hi : ‖∫ x, ψ x • (g x - v) ∂μ‖ ≤ (∫ x, ψ x ∂μ) * η := by
    have hn := norm_integral_le_of_norm_le (f := fun x => ψ x • (g x - v)) hb
      (ae_of_all μ (fun x => by
        by_cases hx : ψ x = 0
        · simp only [hx, zero_smul, norm_zero, zero_mul, le_refl]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ x)]
          exact mul_le_mul_of_nonneg_left (hosc x hx) (hψ x)))
    simpa only [integral_mul_const] using hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  calc
    _ ≤ (∫ x, ψ x ∂μ)⁻¹ * ((∫ x, ψ x ∂μ) * η) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hd.le)
    _ = η := by rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]

theorem integral_weight_pos_of_full_support (ψ : C(X, ℝ)) (hψ : ∀ x, 0 ≤ ψ x)
    (hfull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < μ U) (hψne : ψ ≠ 0) :
    0 < ∫ x, ψ x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg hψ (continuous_compact_integrable μ ℝ ψ)).mpr
  apply hfull
  · exact isOpen_ne_fun ψ.continuous continuous_const
  · by_contra hempty
    apply hψne
    ext x
    by_contra hx
    exact hempty ⟨x, hx⟩

end

end GlobalRegularization
