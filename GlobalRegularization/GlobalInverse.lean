import GlobalRegularization.C1Specification
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Global inverse on the open image

An injective `C¹` map with invertible derivatives on an open Banach-space
domain has a `C¹` inverse on its open image. This constructs the inverse
and proves its regularity using the Banach inverse function theorem.
It does not assume existence of the candidate coordinate map.
-/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem isOpen_image_of_invertible_derivative
    {U : Set E} {A : E → E} (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U)
    (hderiv : ∀ x ∈ U, ∃ T : E ≃L[ℝ] E, HasFDerivAt A (T : E →L[ℝ] E) x) :
    IsOpen (A '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨T, hT⟩ := hderiv x hx
  have hs := (hA.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt' hT le_rfl
  rw [← hs.map_nhds_eq_of_equiv]
  change A ⁻¹' (A '' U) ∈ 𝓝 x
  exact mem_of_superset (hU.mem_nhds hx) (fun y hy => ⟨y, hy, rfl⟩)

theorem contDiffOn_invFunOn_of_injective_derivative
    {U : Set E} {A : E → E} (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U)
    (hinj : Set.InjOn A U)
    (hderiv : ∀ x ∈ U, ∃ T : E ≃L[ℝ] E, HasFDerivAt A (T : E →L[ℝ] E) x) :
    ContDiffOn ℝ 1 (Function.invFunOn A U) (A '' U) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨T, hT⟩ := hderiv x hx
  have hc := hA.contDiffAt (hU.mem_nhds hx)
  have hs := hc.hasStrictFDerivAt' hT le_rfl
  have heq : ∀ᶠ z in 𝓝 x, Function.invFunOn A U (A z) = z :=
    mem_of_superset (hU.mem_nhds hx) (fun z hz => hinj.leftInvOn_invFunOn hz)
  have hi := hc.to_localInverse hT le_rfl
  have hi' : ContDiffAt ℝ 1 (Function.invFunOn A U) (A x) :=
    hi.congr_of_eventuallyEq (hs.localInverse_unique heq)
  exact hi'.contDiffWithinAt

/-- Assemble a genuine ambient `C¹` straightening from an explicitly
constructed injective candidate and its invertible derivatives. -/
def straighteningOfInjectiveDerivative
    {U : Set E} {D : E →L[ℝ] V} {f : E → V} {A : E → E}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hinj : Set.InjOn A U)
    (hderiv : ∀ x ∈ U, ∃ T : E ≃L[ℝ] E, HasFDerivAt A (T : E →L[ℝ] E) x)
    (hdefect : ∀ x ∈ U, D (A x) = D x - f x) : C1Straightening U D f where
  target := A '' U
  target_open := isOpen_image_of_invertible_derivative hU hA hderiv
  forward := A
  backward := Function.invFunOn A U
  forward_maps := fun x hx => ⟨x, hx, rfl⟩
  backward_maps := fun _y hy => Function.invFunOn_mem hy
  left_inverse := hinj.leftInvOn_invFunOn
  right_inverse := fun _y hy => Function.invFunOn_eq hy
  forward_smooth := hA
  backward_smooth := contDiffOn_invFunOn_of_injective_derivative hU hA hinj hderiv
  endpoint_identity := hdefect

end

end GlobalRegularization
