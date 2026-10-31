import GlobalRegularization.HistorySpace
import GlobalRegularization.ScalarRieszRepresentation

/-! Endpoint/derivative decomposition of actual history functionals and
the scalar finite-measure representation. -/

namespace GlobalRegularization

open Set MeasureTheory
open scoped NNReal

noncomputable section

instance (h : ℝ≥0) : T2Space (HistoryInterval h) :=
  inferInstanceAs (T2Space (Set.Icc (-(h : ℝ)) 0))

instance (h : ℝ≥0) : MeasurableSpace (HistoryInterval h) := borel (HistoryInterval h)

instance (h : ℝ≥0) : BorelSpace (HistoryInterval h) := ⟨rfl⟩

variable (h : ℝ≥0) (B V : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem historyFunctional_split (L : C1History h B →L[ℝ] V) :
    ∃ A : B →L[ℝ] V, ∃ D : ContinuousHistory h B →L[ℝ] V,
      ∀ x, L x = A (historyInclusion h B x (historyLeft h)) + D (historyDerivative h B x) := by
  let H := historyCoordinates h B
  let F : (B × ContinuousHistory h B) →L[ℝ] V := L.comp (H.symm : _ →L[ℝ] _)
  refine ⟨F.comp (ContinuousLinearMap.inl ℝ B (ContinuousHistory h B)),
    F.comp (ContinuousLinearMap.inr ℝ B (ContinuousHistory h B)), ?_⟩
  intro x
  change L x = F (historyInclusion h B x (historyLeft h), 0) + F (0, historyDerivative h B x)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  change L x = L (H.symm (H x))
  rw [H.symm_apply_apply]

theorem scalarHistoryFunctional_representation (L : C1History h ℝ →L[ℝ] ℝ) :
    ∃ b : ℝ, ∃ μ ν : Measure (HistoryInterval h), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
      ∀ x, L x = b * historyInclusion h ℝ x (historyLeft h) +
        (∫ t, historyDerivative h ℝ x t ∂μ) - ∫ t, historyDerivative h ℝ x t ∂ν := by
  obtain ⟨A, D, hsplit⟩ := historyFunctional_split h ℝ ℝ L
  obtain ⟨μ, ν, hμ, hν, hrep⟩ := continuousFunctional_riesz_difference D
  refine ⟨A 1, μ, ν, hμ, hν, ?_⟩
  intro x
  have hA (a : ℝ) : A a = A 1 * a := by
    have hm := A.map_smul a (1 : ℝ)
    simpa only [smul_eq_mul, mul_one, mul_comm] using hm
  rw [hsplit, hA, hrep]
  ring

end

end GlobalRegularization
