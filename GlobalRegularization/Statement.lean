import GlobalRegularization.Algebraic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Legacy algebraic specifications

The paper's central assertion is about `C^1([-h,0], ℝ^n)`, an arbitrary open
subset of that Banach space, and the extended-derivative property (e).

These preliminary specifications are retained for compatibility with the
original archive. They are not the main certificate. `MainExistence.mainClaim`
and the finite-state and Hilbert full theorems construct the actual analytic
charts, including smooth inverses, on the genuine history spaces.

The existence claim is intentionally a `def`, NOT a theorem, axiom, or `sorry`.
-/

namespace GlobalRegularization

variable {E V : Type*} [AddCommGroup V]

/-- Logical target of an exact straightening on the domain `U`.

    The actual paper requires the witnessing map to be a `C^1`
    diffeomorphism onto an open subset, a requirement deliberately omitted here.
    Thus this is a WEAKER preliminary target, not a formalization of
    the paper's main theorem. -/
def HasExactAlgebraicStraightening
    (U : Set E) (D : E → V) (f : E → V) : Prop :=
  ∃ A : E → E, ∀ x ∈ U, D (A x) = D x - f x

/-- The known algebraic part of the paper, assuming a witness exists. -/
theorem algebraic_straightening_implies_levels
    (U : Set E) (D : E → V) (f : E → V)
    (h : HasExactAlgebraicStraightening U D f) :
    ∃ A : E → E, ∀ b : V,
      A '' {x | x ∈ U ∧ D x - f x = b} =
        (A '' U) ∩ {y | D y = b} := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, fun b => image_compatibilityLevel U D f A hA b⟩

end GlobalRegularization

namespace GlobalRegularization

section OpenImageTarget

variable {E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An exact *open-image bijective* straightening, formulated on an
    arbitrary open domain. This still does not assert that the bijection
    or its inverse is `C¹`. The full analytic specification is `C1Straightening`. -/
def HasOpenImageAlgebraicStraightening
    (U : Set E) (D : E →L[ℝ] V) (f : U → V) : Prop :=
  ∃ Ω : Set E, IsOpen Ω ∧
    ∃ A : U ≃ Ω,
      ∀ x : U, D (A x : E) = D (x : E) - f x

end OpenImageTarget

end GlobalRegularization
