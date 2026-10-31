import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import GlobalRegularization.Algebraic

/-!
# Exact analytic specification (not an existence proof)

This is the object that the paper must construct. It makes the distinction
between a bijective map and a global ambient C¹ diffeomorphism explicit.
The reusable specification is abstract. MainStatement instantiates it on
the genuine Banach history space constructed in HistorySpace.

No unproved statement is installed as an axiom or theorem.
-/

namespace GlobalRegularization

universe u v

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A global ambient C¹ coordinate change preserving the compatibility
    defect: `D (A x) = D x - f x` on an arbitrary open domain `U`.
    All inverse and regularity conditions are specified, not assumed for
    any particular feedback function. -/
structure C1Straightening (U : Set E) (D : E →L[ℝ] V) (f : E → V) where
  target : Set E
  target_open : IsOpen target
  forward : E → E
  backward : E → E
  forward_maps : Set.MapsTo forward U target
  backward_maps : Set.MapsTo backward target U
  left_inverse : ∀ x ∈ U, backward (forward x) = x
  right_inverse : ∀ y ∈ target, forward (backward y) = y
  forward_smooth : ContDiffOn ℝ 1 forward U
  backward_smooth : ContDiffOn ℝ 1 backward target
  endpoint_identity : ∀ x ∈ U, D (forward x) = D x - f x

/-- The paper's target can now be stated without omitting the requirement
    that the straightening and its inverse be C¹ on open sets. -/
def AdmitsGlobalC1Straightening
    (U : Set E) (D : E →L[ℝ] V) (f : E → V) : Prop :=
  IsOpen U ∧ Nonempty (C1Straightening U D f)

/-- A global C¹ straightening automatically sends the zero compatibility
    level onto the zero hyperplane inside its image. -/
theorem c1_straightening_solution_manifold
    (U : Set E) (D : E →L[ℝ] V) (f : E → V)
    (s : C1Straightening U D f) :
    s.forward '' solutionManifold U D f =
      (s.forward '' U) ∩ zeroHyperplane D := by
  exact image_solutionManifold U D f s.forward s.endpoint_identity

/-- The very same coordinate change straightens every compatibility level. -/
theorem c1_straightening_all_levels
    (U : Set E) (D : E →L[ℝ] V) (f : E → V)
    (s : C1Straightening U D f) (b : V) :
    s.forward '' {x | x ∈ U ∧ D x - f x = b} =
      (s.forward '' U) ∩ {y | D y = b} := by
  exact image_compatibilityLevel U D f s.forward s.endpoint_identity b

end GlobalRegularization
