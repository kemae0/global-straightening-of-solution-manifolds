import GlobalRegularization.C1Specification

/-! A bounded linear endpoint-coordinate replacement, including the
continuous inverse needed by the endpoint-coupling application. -/

namespace GlobalRegularization

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def endpointReplacementCLM (D : E →L[ℝ] V) (Q : V →L[ℝ] E) (N : V ≃L[ℝ] V) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + Q.comp (((N : V →L[ℝ] V) - ContinuousLinearMap.id ℝ V).comp D)

theorem endpointReplacementCLM_coordinate
    (D : E →L[ℝ] V) (Q : V →L[ℝ] E) (hQ : D.comp Q = ContinuousLinearMap.id ℝ V)
    (N : V ≃L[ℝ] V) (x : E) : D (endpointReplacementCLM D Q N x) = N (D x) := by
  have hq (v : V) : D (Q v) = v := congrArg (fun L : V →L[ℝ] V => L v) hQ
  change D (x + Q (N (D x) - D x)) = N (D x)
  rw [map_add, hq]
  abel

theorem endpointReplacementCLM_left_inverse
    (D : E →L[ℝ] V) (Q : V →L[ℝ] E) (hQ : D.comp Q = ContinuousLinearMap.id ℝ V)
    (N : V ≃L[ℝ] V) (x : E) :
    endpointReplacementCLM D Q N.symm (endpointReplacementCLM D Q N x) = x := by
  change endpointReplacementCLM D Q N x +
    Q (N.symm (D (endpointReplacementCLM D Q N x)) - D (endpointReplacementCLM D Q N x)) = x
  rw [endpointReplacementCLM_coordinate D Q hQ N, N.symm_apply_apply]
  change x + Q (N (D x) - D x) + Q (D x - N (D x)) = x
  rw [add_assoc, ← map_add]
  have hz : N (D x) - D x + (D x - N (D x)) = 0 := by abel
  rw [hz, map_zero, add_zero]

def endpointReplacementCLE (D : E →L[ℝ] V) (Q : V →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ V) (N : V ≃L[ℝ] V) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toLinearMap := (endpointReplacementCLM D Q N).toLinearMap
      invFun := endpointReplacementCLM D Q N.symm
      left_inv := endpointReplacementCLM_left_inverse D Q hQ N
      right_inv := fun x => by
        exact endpointReplacementCLM_left_inverse D Q hQ N.symm x }
  continuous_toFun := (endpointReplacementCLM D Q N).continuous
  continuous_invFun := (endpointReplacementCLM D Q N.symm).continuous

end

end GlobalRegularization
