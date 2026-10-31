import GlobalRegularization.EndpointLinearEquiv
import GlobalRegularization.MainExistence

/-! Analytic endpoint coupling: composing the constructed nonlinear
chart with an explicit bounded linear endpoint-coordinate change. -/

namespace GlobalRegularization

open Set
open scoped NNReal

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def C1Straightening.postcompose_endpoint
    {U : Set E} {D : E →L[ℝ] V} {f : E → V} (s : C1Straightening U D f)
    (Q : V →L[ℝ] E) (hQ : D.comp Q = ContinuousLinearMap.id ℝ V) (N : V ≃L[ℝ] V) :
    C1Straightening U D (fun x => D x - N (D x - f x)) := by
  let T := endpointReplacementCLE D Q hQ N
  refine
    { target := T.symm ⁻¹' s.target
      target_open := s.target_open.preimage T.symm.continuous
      forward := fun x => T (s.forward x)
      backward := fun y => s.backward (T.symm y)
      forward_maps := ?_
      backward_maps := fun y hy => s.backward_maps hy
      left_inverse := ?_
      right_inverse := ?_
      forward_smooth := T.contDiff.comp_contDiffOn s.forward_smooth
      backward_smooth := s.backward_smooth.comp T.symm.contDiff.contDiffOn (fun y hy => hy)
      endpoint_identity := ?_ }
  · intro x hx
    change T.symm (T (s.forward x)) ∈ s.target
    rw [T.symm_apply_apply]
    exact s.forward_maps hx
  · intro x hx
    rw [T.symm_apply_apply]
    exact s.left_inverse x hx
  · intro y hy
    rw [s.right_inverse (T.symm y) hy, T.apply_symm_apply]
  · intro x hx
    change D (endpointReplacementCLM D Q N (s.forward x)) = _
    rw [endpointReplacementCLM_coordinate D Q hQ N, s.endpoint_identity x hx]
    abel

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B]

theorem property_e_endpoint_coupling
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (g : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) g)
    (M : B →L[ℝ] B) (N : B ≃L[ℝ] B)
    (hN : (N : B →L[ℝ] B) = ContinuousLinearMap.id ℝ B - M) :
    Nonempty (C1Straightening U (endpointDerivative h B)
      (fun x => M (endpointDerivative h B x) + g x)) := by
  let gt : C1History h B → B := fun x => N.symm (g x)
  have het : HasExtendedDerivative U (historyInclusion h B) gt := by
    have ht := he.linear_pullback (κ := historyInclusion h B) hU (ContinuousLinearMap.id ℝ (C1History h B))
      (ContinuousLinearMap.id ℝ (ContinuousHistory h B)) (N.symm : B →L[ℝ] B) (by simp)
    simpa only [ContinuousLinearMap.id_apply, Set.preimage_id, gt] using ht
  obtain ⟨s⟩ := property_e_localized_straightening h B hh U hU gt het ((h : ℝ) / 2) 1
    (by positivity) zero_lt_one
  let Q := terminalCorrection h B 1 zero_lt_one
  let chart := s.toC1Straightening.postcompose_endpoint Q (terminalCorrection_endpoint h B 1 zero_lt_one) N
  have heq : (fun x => endpointDerivative h B x - N (endpointDerivative h B x - gt x)) =
      (fun x => M (endpointDerivative h B x) + g x) := by
    funext x
    rw [map_sub]
    change endpointDerivative h B x - (N (endpointDerivative h B x) - N (N.symm (g x))) = _
    rw [N.apply_symm_apply]
    have hn := congrArg (fun L : B →L[ℝ] B => L (endpointDerivative h B x)) hN
    change N (endpointDerivative h B x) = endpointDerivative h B x - M (endpointDerivative h B x) at hn
    rw [hn]
    abel
  rw [← heq]
  exact ⟨chart⟩

end

end GlobalRegularization
