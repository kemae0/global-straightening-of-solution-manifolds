import GlobalRegularization.C1Specification
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! A chart with an exact compatibility identity gives an explicit
bounded right inverse for the derivative of the compatibility defect. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem C1Straightening.forward_backward_derivative
    {U : Set E} {D : E →L[ℝ] V} {f : E → V}
    (s : C1Straightening U D f) (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    (fderiv ℝ s.forward x).comp (fderiv ℝ s.backward (s.forward x)) =
      ContinuousLinearMap.id ℝ E := by
  have hy := s.forward_maps hx
  have hF := ((s.forward_smooth.differentiableOn le_rfl x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hB := ((s.backward_smooth.differentiableOn le_rfl _ hy).differentiableAt
    (s.target_open.mem_nhds hy)).hasFDerivAt
  have hF' : HasFDerivAt s.forward (fderiv ℝ s.forward x) (s.backward (s.forward x)) := by
    rw [s.left_inverse x hx]
    exact hF
  have hcomp := hF'.comp (s.forward x) hB
  have hevent : (s.forward ∘ s.backward) =ᶠ[𝓝 (s.forward x)] (fun z => z) := by
    filter_upwards [s.target_open.mem_nhds hy] with z hz
    exact s.right_inverse z hz
  exact hcomp.unique ((hasFDerivAt_id (s.forward x)).congr_of_eventuallyEq hevent)

theorem C1Straightening.defect_derivative
    {U : Set E} {D : E →L[ℝ] V} {f : E → V}
    (s : C1Straightening U D f) (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fun y => D y - f y) x = D.comp (fderiv ℝ s.forward x) := by
  have hF := ((s.forward_smooth.differentiableOn le_rfl x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcomp := D.hasFDerivAt.comp x hF
  have hevent : (fun y => D y - f y) =ᶠ[𝓝 x] (D ∘ s.forward) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (s.endpoint_identity y hy).symm
  exact (hcomp.congr_of_eventuallyEq hevent).fderiv

def C1Straightening.defectRightInverse
    {U : Set E} {D : E →L[ℝ] V} {f : E → V}
    (s : C1Straightening U D f) (Q : V →L[ℝ] E) (x : E) : V →L[ℝ] E :=
  (fderiv ℝ s.backward (s.forward x)).comp Q

theorem C1Straightening.defectRightInverse_spec
    {U : Set E} {D : E →L[ℝ] V} {f : E → V}
    (s : C1Straightening U D f) (hU : IsOpen U) (Q : V →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ V) {x : E} (hx : x ∈ U) :
    (fderiv ℝ (fun y => D y - f y) x).comp (s.defectRightInverse Q x) =
      ContinuousLinearMap.id ℝ V := by
  rw [s.defect_derivative hU hx]
  apply ContinuousLinearMap.ext
  intro a
  change D ((fderiv ℝ s.forward x) ((fderiv ℝ s.backward (s.forward x)) (Q a))) = a
  have hi := congrArg (fun L : E →L[ℝ] E => L (Q a)) (s.forward_backward_derivative hU hx)
  change (fderiv ℝ s.forward x) ((fderiv ℝ s.backward (s.forward x)) (Q a)) = Q a at hi
  rw [hi]
  exact congrArg (fun L : V →L[ℝ] V => L a) hQ

theorem C1Straightening.defectRightInverse_continuousOn
    {U : Set E} {D : E →L[ℝ] V} {f : E → V}
    (s : C1Straightening U D f) (Q : V →L[ℝ] E) :
    ContinuousOn (s.defectRightInverse Q) U := by
  have hc := s.backward_smooth.continuousOn_fderiv_of_isOpen s.target_open le_rfl
  have hcomp := hc.comp s.forward_smooth.continuousOn s.forward_maps
  have hfixed : Continuous (fun L : E →L[ℝ] E => L.comp Q) := by fun_prop
  exact hfixed.comp_continuousOn hcomp

end

end GlobalRegularization
