import GlobalRegularization.C1Specification
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A genuine nonlinear global special case

If an observation `R` annihilates a correction operator `Q`, then
`x ↦ x - Q (G (R x))` is a global `C¹` diffeomorphism for every globally
`C¹` map `G`. Its restriction to any open set is a `C¹` straightening
provided `D Q = id`. This theorem does not address general property (e).
-/

namespace GlobalRegularization

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def nonlinearRemoteShear (R : E →L[ℝ] V) (Q : V →L[ℝ] E)
    (G : V → V) (x : E) : E := x - Q (G (R x))

theorem nonlinearRemoteShear_preserves_observation
    (R : E →L[ℝ] V) (Q : V →L[ℝ] E) (hRQ : R.comp Q = 0)
    (G : V → V) (x : E) : R (nonlinearRemoteShear R Q G x) = R x := by
  have hz : R (Q (G (R x))) = 0 := congrArg (fun T : V →L[ℝ] V => T (G (R x))) hRQ
  simp [nonlinearRemoteShear, hz]

def nonlinearRemoteShearEquiv
    (R : E →L[ℝ] V) (Q : V →L[ℝ] E) (hRQ : R.comp Q = 0)
    (G : V → V) : E ≃ E where
  toFun := nonlinearRemoteShear R Q G
  invFun := fun x => x + Q (G (R x))
  left_inv := by
    intro x
    change nonlinearRemoteShear R Q G x + Q (G (R (nonlinearRemoteShear R Q G x))) = x
    rw [nonlinearRemoteShear_preserves_observation R Q hRQ]
    simp [nonlinearRemoteShear]
  right_inv := by
    intro x
    have hz : R (Q (G (R x))) = 0 := congrArg (fun T : V →L[ℝ] V => T (G (R x))) hRQ
    simp [nonlinearRemoteShear, hz]

def nonlinearRemoteShearHomeomorph
    (R : E →L[ℝ] V) (Q : V →L[ℝ] E) (hRQ : R.comp Q = 0)
    (G : V → V) (hG : ContDiff ℝ 1 G) : E ≃ₜ E where
  toEquiv := nonlinearRemoteShearEquiv R Q hRQ G
  continuous_toFun := (contDiff_id.sub (Q.contDiff.comp (hG.comp R.contDiff))).continuous
  continuous_invFun := (contDiff_id.add (Q.contDiff.comp (hG.comp R.contDiff))).continuous

def nonlinearRemoteStraightening
    (U : Set E) (hU : IsOpen U) (D R : E →L[ℝ] V) (Q : V →L[ℝ] E)
    (hRQ : R.comp Q = 0) (hDQ : D.comp Q = ContinuousLinearMap.id ℝ V)
    (G : V → V) (hG : ContDiff ℝ 1 G) :
    C1Straightening U D (fun x => G (R x)) where
  target := nonlinearRemoteShear R Q G '' U
  target_open := (nonlinearRemoteShearHomeomorph R Q hRQ G hG).isOpenMap U hU
  forward := nonlinearRemoteShear R Q G
  backward := fun x => x + Q (G (R x))
  forward_maps := fun x hx => ⟨x, hx, rfl⟩
  backward_maps := by
    rintro y ⟨x, hx, rfl⟩
    change (nonlinearRemoteShearEquiv R Q hRQ G).symm
      ((nonlinearRemoteShearEquiv R Q hRQ G) x) ∈ U
    simpa only [Equiv.symm_apply_apply] using hx
  left_inverse := fun x _ => (nonlinearRemoteShearEquiv R Q hRQ G).left_inv x
  right_inverse := fun y _ => (nonlinearRemoteShearEquiv R Q hRQ G).right_inv y
  forward_smooth := (contDiff_id.sub (Q.contDiff.comp (hG.comp R.contDiff))).contDiffOn
  backward_smooth := (contDiff_id.add (Q.contDiff.comp (hG.comp R.contDiff))).contDiffOn
  endpoint_identity := by
    intro x hx
    have heq : D (Q (G (R x))) = G (R x) :=
      congrArg (fun T : V →L[ℝ] V => T (G (R x))) hDQ
    simp [nonlinearRemoteShear, heq]

end

end GlobalRegularization
