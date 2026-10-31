import GlobalRegularization.C1Specification
import GlobalRegularization.ComplexifiedSpectrum

/-! A certificate extracted from the constructed derivative, and its
spectral conclusions after genuine complexification. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def C1Straightening.HasTriangularDerivative {U : Set E} {D : E →L[ℝ] B} {f : E → B}
    (chart : C1Straightening U D f) : Prop :=
  ∀ x ∈ U, ∃ Q : ℕ → B →L[ℝ] E, ∃ A : ℕ → E →L[ℝ] B,
    (∀ i j, i ≤ j → (A i).comp (Q j) = 0) ∧
      Tendsto (triangularPartial Q A) atTop (𝓝 (fderiv ℝ chart.forward x - 1))

theorem C1Straightening.HasTriangularDerivative.spectrum_subset
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} {chart : C1Straightening U D f}
    (hc : chart.HasTriangularDerivative) {x : E} (hx : x ∈ U) :
    spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) ⊆ {1} := by
  obtain ⟨Q, A, hann, hlim⟩ := hc x hx
  have heq : 1 + (fderiv ℝ chart.forward x - 1) = fderiv ℝ chart.forward x := by abel
  simpa only [heq] using complexified_spectrum_one_add_subset_of_triangular_limit Q A hann _ hlim

theorem C1Straightening.HasTriangularDerivative.spectrum_eq [Nontrivial E]
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} {chart : C1Straightening U D f}
    (hc : chart.HasTriangularDerivative) {x : E} (hx : x ∈ U) :
    spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  obtain ⟨Q, A, hann, hlim⟩ := hc x hx
  have heq : 1 + (fderiv ℝ chart.forward x - 1) = fderiv ℝ chart.forward x := by abel
  simpa only [heq] using complexified_spectrum_one_add_eq_of_triangular_limit Q A hann _ hlim

end

end GlobalRegularization
