import GlobalRegularization.HilbertNormalizedExistence
import GlobalRegularization.MainExistence
import GlobalRegularization.TriangularDerivativeConjugate

/-! The global Hilbert-valued theorem for every positive history length.
The spectral equality is stated with the necessary nontriviality condition. -/

namespace GlobalRegularization

open Set TopologicalSpace
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace B] [SeparableSpace B]
theorem property_e_Hilbert_localized_straightening_with_certificate
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧ chart.toC1Straightening.HasTriangularDerivative := by
  let R := historyRescaleEquiv h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  let T : C1History 1 B →L[ℝ] C1History h B := R.symm
  have hInv : (h : ℝ)⁻¹ * (h : ℝ) = 1 := inv_mul_cancel₀ hh.ne'
  let S := continuousHistoryRescaleCLM 1 h B (h : ℝ)⁻¹ (inv_nonneg.mpr hh.le) hInv
  let P : B →L[ℝ] B := (h : ℝ) • ContinuousLinearMap.id ℝ B
  have hcomm : (historyInclusion h B).comp T = S.comp (historyInclusion 1 B) :=
    historyRescaleEquiv_symm_inclusion h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  let g : C1History 1 B → B := fun x => P (f (T x))
  have hU₁ : IsOpen (R.symm ⁻¹' U) := hU.preimage R.symm.continuous
  have he₁ : HasExtendedDerivative (R.symm ⁻¹' U) (historyInclusion 1 B) g :=
    he.linear_pullback hU T S P hcomm
  obtain ⟨s, hiso, htri⟩ := property_e_Hilbert_normalized_straightening B (R.symm ⁻¹' U) hU₁ g he₁
    (τ / (h : ℝ)) ε (div_pos hτ hh) hε
  let q := historyScaleTime 1 h (h : ℝ)⁻¹ (inv_nonneg.mpr hh.le) hInv
  have hval : ∀ y t, historyInclusion h B (R.symm y) t = historyInclusion 1 B y (q t) :=
    historyRescaleEquiv_symm_value h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  have hzero : q (historyRight h) = historyRight 1 := by
    apply Subtype.ext
    simp only [q, historyScaleTime, historyRight, mul_zero]
  have hremote : ∀ t : HistoryInterval h, (t : ℝ) ≤ -τ → (q t : ℝ) ≤ -(τ / (h : ℝ)) := by
    intro t ht
    have hm := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hh.le)
    simpa only [q, historyScaleTime, mul_neg, div_eq_mul_inv, mul_comm] using hm
  have hD : ∀ y, endpointDerivative h B (R.symm y) = (h : ℝ)⁻¹ • endpointDerivative 1 B y :=
    historyRescaleEquiv_symm_endpoint h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  have hg : ∀ x, (h : ℝ)⁻¹ • g (R x) = f x := by
    intro x
    change (h : ℝ)⁻¹ • ((h : ℝ) • f (R.symm (R x))) = f x
    rw [R.symm_apply_apply, inv_smul_smul₀ hh.ne']
  have hnorm : ∀ z, ‖historyInclusion h B (R.symm z)‖ ≤ ‖historyInclusion 1 B z‖ :=
    norm_historyRescaleEquiv_symm_value_le h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  let chart := localizedStraightening_time_transport h B R q U f g τ (τ / (h : ℝ)) ε (h : ℝ)⁻¹
    hval hzero hremote hD hg hnorm s
  refine ⟨chart, localizedStraightening_time_transport_isotopy h B R q U f g τ (τ / (h : ℝ)) ε (h : ℝ)⁻¹
    hval hzero hremote hD hg hnorm s hiso, ?_⟩
  apply C1Straightening.HasTriangularDerivative.conjugate s.toC1Straightening htri hU₁ R chart.toC1Straightening
  · intro x hx
    simpa only [mem_preimage, R.symm_apply_apply] using hx
  · rfl

theorem property_e_Hilbert_full_straightening [Nontrivial B]
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
        ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  letI : Nontrivial (C1History h B) := Function.Injective.nontrivial (historyCoordinates h B).symm.injective
  obtain ⟨chart, hi, ht⟩ := property_e_Hilbert_localized_straightening_with_certificate h B hh U hU f he τ ε hτ hε
  exact ⟨chart, hi, fun x hx => ht.spectrum_eq hx⟩

theorem property_e_Hilbert_straightening_spectrum_inclusion
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
        ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) ⊆ {1} := by
  obtain ⟨chart, hi, ht⟩ := property_e_Hilbert_localized_straightening_with_certificate h B hh U hU f he τ ε hτ hε
  exact ⟨chart, hi, fun x hx => ht.spectrum_subset hx⟩

end

end GlobalRegularization
