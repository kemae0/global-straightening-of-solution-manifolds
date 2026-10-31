import GlobalRegularization.SplitFibers

/-! Tangent spaces of the split compatibility fibers, calculated from
actual local fiber parametrizations and identified with the defect kernel. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem C1Straightening.backward_forward_derivative
    {U : Set E} {D : E →L[ℝ] B} {f : E → B}
    (s : C1Straightening U D f) (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    (fderiv ℝ s.backward (s.forward x)).comp (fderiv ℝ s.forward x) = ContinuousLinearMap.id ℝ E := by
  have hf := (s.forward_smooth.contDiffAt (hU.mem_nhds hx)).differentiableAt le_rfl
  have hb := (s.backward_smooth.contDiffAt (s.target_open.mem_nhds (s.forward_maps hx))).differentiableAt le_rfl
  have hd := hb.hasFDerivAt.comp x hf.hasFDerivAt
  have hevent : (s.backward ∘ s.forward) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact s.left_inverse y hy
  exact hd.unique ((hasFDerivAt_id x).congr_of_eventuallyEq hevent)

def C1Straightening.fiberTangentInclusion
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} (s : C1Straightening U D f) (x : E) :
    LinearMap.ker D →L[ℝ] E :=
  (fderiv ℝ s.backward (s.forward x)).comp (LinearMap.ker D).subtypeL

theorem C1Straightening.fiber_parameter_derivative
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} (s : C1Straightening U D f)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun z : LinearMap.ker D => s.backward (s.forward x + z)) (s.fiberTangentInclusion x) 0 := by
  have hb := (s.backward_smooth.contDiffAt (s.target_open.mem_nhds (s.forward_maps hx))).differentiableAt le_rfl
  have hg : HasFDerivAt (fun z : LinearMap.ker D => s.forward x + z) (LinearMap.ker D).subtypeL 0 :=
    (LinearMap.ker D).subtypeL.hasFDerivAt.const_add _
  have hb' : HasFDerivAt s.backward (fderiv ℝ s.backward (s.forward x))
      (s.forward x + (0 : LinearMap.ker D)) := by simpa using hb.hasFDerivAt
  exact hb'.comp (f := fun z : LinearMap.ker D => s.forward x + (z : E)) (0 : LinearMap.ker D) hg

theorem C1Straightening.fiberTangent_range
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} (s : C1Straightening U D f)
    (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    LinearMap.range (s.fiberTangentInclusion x) =
      LinearMap.ker (fderiv ℝ (fun y => D y - f y) x) := by
  have hfb := s.forward_backward_derivative hU hx
  have hbf := s.backward_forward_derivative hU hx
  have he (z : E) : (fderiv ℝ s.forward x) ((fderiv ℝ s.backward (s.forward x)) z) = z :=
    congrArg (fun L : E →L[ℝ] E => L z) hfb
  have hi (z : E) : (fderiv ℝ s.backward (s.forward x)) ((fderiv ℝ s.forward x) z) = z :=
    congrArg (fun L : E →L[ℝ] E => L z) hbf
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    change (fderiv ℝ (fun y => D y - f y) x) ((fderiv ℝ s.backward (s.forward x)) z) = 0
    rw [s.defect_derivative hU hx, ContinuousLinearMap.comp_apply, he]
    exact z.property
  · intro hv
    change (fderiv ℝ (fun y => D y - f y) x) v = 0 at hv
    rw [s.defect_derivative hU hx, ContinuousLinearMap.comp_apply] at hv
    refine ⟨⟨(fderiv ℝ s.forward x) v, hv⟩, ?_⟩
    exact hi v

end

end GlobalRegularization
