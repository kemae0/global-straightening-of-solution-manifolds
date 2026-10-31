import GlobalRegularization.LocalC1Approximation
import GlobalRegularization.UnitHistoryOperatorNorm
import GlobalRegularization.UnitHistoryObservations

/-! Globally bounded cylindrical approximants, with the full local `C¹`
operator-norm approximation and terminal derivative annihilation, for
property-(e) functionals on actual normalized finite-state histories. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable (B V : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem property_e_normalized_bounded_C1_approximants
    (U : Set (C1History 1 B)) (hU : IsOpen U) (f : C1History 1 B → V)
    (he : HasExtendedDerivative U (historyInclusion 1 B) f) :
    ∃ fm : ℕ → C1History 1 B → V,
      (∀ n, ContDiff ℝ 1 (fm n)) ∧ (∀ n, Bornology.IsBounded (range (fm n))) ∧
      LocalC1Approximation U f fm ∧
      (∀ n, ∃ hat : LinearMap.range (unitHistoryBernsteinCLM B n) → V,
        ContDiff ℝ 1 hat ∧ ∀ x, fm n x = hat ((unitHistoryBernsteinCLM B n).rangeRestrict x)) ∧
      ∀ (n : ℕ) (δ : ℝ) (hδ : 0 < δ), δ / 2 < 1 / (n + 1 : ℝ) → ∀ x,
        (fderiv ℝ (fm n) x).comp (terminalCorrection 1 B δ hδ) = 0 := by
  have hfixed : ∀ x ∈ U, Tendsto (fun n => (fderiv ℝ f x).comp
      (unitHistoryBernsteinCLM B n - ContinuousLinearMap.id ℝ (C1History 1 B))) atTop (𝓝 0) := by
    intro x hx
    apply he.tendsto_derivative_comp _ hx
    simpa only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id] using
      unitHistoryBernstein_operator_tendsto_zero B
  obtain ⟨fm, hsmooth, hbounded, hfactor, happ⟩ :=
    exists_bounded_local_C1_cylindrical_family U hU f he.c1
      (unitHistoryBernsteinCLM B) (norm_unitHistoryBernsteinCLM_le B)
      (unitHistoryBernstein_strong B) (unitHistoryBernstein_finite_range B) hfixed
  refine ⟨fm, hsmooth, hbounded, happ, hfactor, ?_⟩
  intro n δ hδ hshort x
  obtain ⟨hat, hhat, hfact⟩ := hfactor n
  let R := (unitHistoryBernsteinCLM B n).rangeRestrict
  have hzero : R.comp (terminalCorrection 1 B δ hδ) = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun P : B →L[ℝ] C1History 1 B => P a)
      (unitHistoryBernstein_annihilates_terminal B n δ hδ hshort)
  have hfun : fm n = fun y => hat (R y) := funext hfact
  have hcomp := ((hhat.differentiable_one (R x)).hasFDerivAt).comp x R.hasFDerivAt
  have hD : fderiv ℝ (fm n) x = (fderiv ℝ hat (R x)).comp R := by
    rw [hfun]
    exact hcomp.fderiv
  rw [hD, ContinuousLinearMap.comp_assoc, hzero, ContinuousLinearMap.comp_zero]

end

end GlobalRegularization
