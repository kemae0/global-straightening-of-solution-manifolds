import Mathlib.Tactic
import GlobalRegularization.C1Specification
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Property (e): the exact extended-derivative hypothesis

The manuscript calls property (e) an extension of the Fréchet derivative
from C¹ histories to continuous histories with jointly continuous action.
This file specifies that property using an abstract continuous inclusion
`ι : E →L[ℝ] C`.

This is NOT a proof that any given f has the property; it is a typed
statement of the analytic hypothesis that must be linked to a concrete
history-space construction.


-/

namespace GlobalRegularization

universe u v w

variable {E : Type u} {C : Type v} {V : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The exact (e) hypothesis: an extended derivative `C →L[ℝ] V`
whose restriction is the Fréchet derivative on `E`, with jointly
continuous evaluation on the open domain. -/
structure HasExtendedDerivative
    (U : Set E) (ι : E →L[ℝ] C) (f : E → V) : Prop where
  c1 : ContDiffOn ℝ 1 f U
  exists_extension : ∃ extension : E → (C →L[ℝ] V),
    (∀ x ∈ U, fderiv ℝ f x = (extension x).comp ι) ∧
    ContinuousOn (fun p : E × C => extension p.1 p.2) (U.prod Set.univ)

/-- Property (e) kills any correction family whose continuous-history
operator norms tend to zero. This is the last step in the paper's proof
of the main theorem once terminal straightening has been constructed. -/
theorem HasExtendedDerivative.tendsto_derivative_comp
    {U : Set E} {ι : E →L[ℝ] C} {f : E → V}
    (he : HasExtendedDerivative U ι f)
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : ℕ → B →L[ℝ] E) {x : E} (hx : x ∈ U)
    (hQ : Filter.Tendsto (fun n => ι.comp (Q n)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (fderiv ℝ f x).comp (Q n)) Filter.atTop (nhds 0) := by
  obtain ⟨ext, hagrees, hcont⟩ := he.exists_extension
  have ht := ((ContinuousLinearMap.compL ℝ B C V) (ext x)).continuous.tendsto 0
  have h := ht.comp hQ
  simpa only [ContinuousLinearMap.compL_apply, map_zero,
    hagrees x hx, ContinuousLinearMap.comp_assoc] using h

/-- A legacy abstract target, not a theorem and not the main certificate.
The concrete history-space claims are proved in `MainExistence`,
`TerminalExistence`, `FiniteFullTheorem`, and `HilbertExistence`. -/
def MainTheoremTarget
    (U : Set E) (ι : E →L[ℝ] C) (D : E →L[ℝ] V)
    (f : E → V) : Prop :=
  IsOpen U → HasExtendedDerivative U ι f →
    AdmitsGlobalC1Straightening U D f

end GlobalRegularization
