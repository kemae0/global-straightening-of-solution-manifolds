import Mathlib.Tactic

/-!
# Explicit global straightening for a linear remote observation

An elementary, genuinely global special case: if `D Q = id` and `R Q = 0`,
then `x ↦ x - Q (R x)` is an additive equivalence, with inverse
`x ↦ x + Q (R x)`, and its endpoint coordinate is `D x - R x`.

For histories, choose `D φ = φ'(0)` and `R φ = φ'(t₀)` at a fixed `t₀ < 0`,
with `Q` supported sufficiently close to zero. HistorySpace and
BoundaryLayer construct the analytic history space and corrections;
this file records the purely additive part.


-/

namespace GlobalRegularization

section RemoteShear

variable {E V : Type*} [AddCommGroup E] [AddCommGroup V]

/-- Correction along a direction invisible to the remote observation. -/
def remoteShear (R : E →+ V) (Q : V →+ E) (x : E) : E :=
  x - Q (R x)

/-- If the remote observation does not see the correction direction,
then the remote observation is invariant under the correction. -/
theorem remoteShear_preserves_remote
    (R : E →+ V) (Q : V →+ E)
    (hRQ : ∀ v : V, R (Q v) = 0) (x : E) :
    R (remoteShear R Q x) = R x := by
  simp [remoteShear, map_sub, hRQ]

/-- The correction is inverted by adding back the same remote value. -/
theorem remoteShear_left_inverse
    (R : E →+ V) (Q : V →+ E)
    (hRQ : ∀ v : V, R (Q v) = 0) (x : E) :
    remoteShear R Q (x + Q (R x)) = x := by
  have h : R (x + Q (R x)) = R x := by
    rw [map_add, hRQ]
    simp
  simp [remoteShear, h]

/-- The converse inverse identity. -/
theorem remoteShear_right_inverse
    (R : E →+ V) (Q : V →+ E)
    (hRQ : ∀ v : V, R (Q v) = 0) (x : E) :
    remoteShear R Q x + Q (R (remoteShear R Q x)) = x := by
  rw [remoteShear_preserves_remote R Q hRQ x]
  simp [remoteShear]

/-- A global additive equivalence realizing the remote-history shear. -/
def remoteShearEquiv
    (R : E →+ V) (Q : V →+ E)
    (hRQ : ∀ v : V, R (Q v) = 0) : E ≃ E where
  toFun := remoteShear R Q
  invFun := fun x => x + Q (R x)
  left_inv := remoteShear_right_inverse R Q hRQ
  right_inv := remoteShear_left_inverse R Q hRQ

/-- Exact endpoint-defect identity for the shear. -/
theorem remoteShear_endpoint
    (D : E →+ V) (R : E →+ V) (Q : V →+ E)
    (hDQ : ∀ v : V, D (Q v) = v) (x : E) :
    D (remoteShear R Q x) = D x - R x := by
  simp [remoteShear, map_sub, hDQ]

end RemoteShear

end GlobalRegularization
