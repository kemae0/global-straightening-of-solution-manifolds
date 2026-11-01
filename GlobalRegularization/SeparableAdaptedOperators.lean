import GlobalRegularization.MatrixAdaptedAdjoint
import GlobalRegularization.AtomFreeRepresentation
import GlobalRegularization.IntervalReferenceMeasure
import GlobalRegularization.HistorySeparable
import GlobalRegularization.CommonDominatingMeasure
import GlobalRegularization.DenseDualApproximation
import GlobalRegularization.FullImageDomination

/-! A common adapted approximation for a separable family of history
functionals. The common measure dominates the actual signed matrix measures
throughout the family, using total-variation continuity. Empty families
are included. -/

namespace GlobalRegularization

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology

noncomputable section

theorem adaptedTerminalWidth_antitone (h : ℝ≥0) : Antitone (adaptedTerminalWidth h) := by
  intro m n hmn
  apply div_le_div_of_nonneg_left h.coe_nonneg (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 2

theorem exists_adapted_operators_for_separable_family
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (S : Set (C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) (hsep : IsSeparable S)
    (hzero : ∀ L ∈ S, Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ)
      (adaptedTerminalWidth h m) (adaptedTerminalWidth_pos h hh m))) atTop (𝓝 0)) :
    ∃ P : ℕ → C1History h (Fin n → ℝ) →L[ℝ] C1History h (Fin n → ℝ),
    ∃ C : ℝ, 0 < C ∧ (∀ m, ‖P m‖ ≤ C) ∧
      (∀ x, Tendsto (fun m => P m x) atTop (𝓝 x)) ∧
      (∀ m, FiniteDimensional ℝ (LinearMap.range (P m))) ∧
      (∀ L ∈ S, Tendsto (fun m => L.comp (P m -
        ContinuousLinearMap.id ℝ (C1History h (Fin n → ℝ)))) atTop (𝓝 0)) ∧
      ∀ m δ (hδ : 0 < δ), δ / 2 < adaptedTerminalWidth h m →
        (P m).comp (terminalCorrection h (Fin n → ℝ) δ hδ) = 0 := by
  obtain ⟨ν, hν, hνatom, hfull, hdom⟩ := exists_full_image_totalVariation_dominator h hh n S hsep hzero
  letI := hν
  let P := adaptedHistoryOperator h (Fin n → ℝ) ν
  let C := max 1 ‖(historyCoordinates h (Fin n → ℝ)).symm.toContinuousLinearMap‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hP : ∀ m, ‖P m‖ ≤ C := fun m =>
    (adaptedHistoryOperator_uniform_bound h (Fin n → ℝ) ν m).trans (le_max_right _ _)
  refine ⟨P, C, hC, hP, adaptedHistoryOperator_strong h (Fin n → ℝ) ν hfull,
    adaptedHistoryOperator_finite_range h (Fin n → ℝ) ν, ?_,
    adaptedHistoryOperator_annihilates_terminal h (Fin n → ℝ) ν⟩
  intro L hLS
  let μ := fun i j => (historySignedMatrix h n L i j).toJordanDecomposition.posPart
  let ρ := fun i j => (historySignedMatrix h n L i j).toJordanDecomposition.negPart
  have hac (i j : Fin n) : μ i j ≪ ν ∧ ρ i j ≪ ν :=
    (SignedMeasure.totalVariation_absolutelyContinuous_iff _ ν).mp (hdom L hLS i j)
  have hatom (i j : Fin n) : μ i j {historyRight h} = 0 ∧ ρ i j {historyRight h} = 0 := by
    have hz := (signed_totalVariation_singleton_zero_iff (historySignedMatrix h n L i j) (historyRight h)).mpr
      (historySignedMatrix_endpoint_zero h hh n L (hzero L hLS) i j)
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hz
  have hrep (x : C1History h (Fin n → ℝ)) (i : Fin n) :
      L x i = historyEndpointPart h n L (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
        ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
          ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ρ i j) := by
    simpa only [signedIntegralFunctional_apply, continuousVectorComponent_apply] using
      historyFunctional_signed_matrix_representation h n L x i
  exact matrixHistoryFunctional_adapted_adjoint h n L (historyEndpointPart h n L) μ ρ hrep ν hfull
    (fun i j => (hac i j).1) (fun i j => (hac i j).2)
    (fun i j => (hatom i j).1) (fun i j => (hatom i j).2)

end

end GlobalRegularization
