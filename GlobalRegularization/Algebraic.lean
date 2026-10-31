import Mathlib.Tactic

/-!
# Algebraic consequences of a global straightening

The source paper is "On global regularization of solution manifolds".
This file isolates statements that depend only on the exact compatibility
identity, not on differentiability or the existence of the chart.
These consequences are conditional on an exact coordinate identity.
-/

namespace GlobalRegularization

section Compatibility

variable {E V : Type*} [AddCommGroup V]

/-- Histories in `U` satisfying the compatibility equation `D x = f x`. -/
def solutionManifold (U : Set E) (D : E → V) (f : E → V) : Set E :=
  {x | x ∈ U ∧ D x = f x}

/-- The zero-compatibility hyperplane. -/
def zeroHyperplane (D : E → V) : Set E :=
  {x | D x = 0}

/-- Exact compatibility straightening implies the zero-level identity. -/
theorem compatibility_iff_zero
    (U : Set E) (D : E → V) (f : E → V) (A : E → E)
    (hA : ∀ x ∈ U, D (A x) = D x - f x)
    {x : E} (hx : x ∈ U) :
    D x = f x ↔ D (A x) = 0 := by
  rw [hA x hx]
  exact (sub_eq_zero).symm

/-- A straightening maps the entire solution manifold exactly onto
    the zero hyperplane restricted to the image of the domain. -/
theorem image_solutionManifold
    (U : Set E) (D : E → V) (f : E → V) (A : E → E)
    (hA : ∀ x ∈ U, D (A x) = D x - f x) :
    A '' solutionManifold U D f = (A '' U) ∩ zeroHyperplane D := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxU, hxF⟩, rfl⟩
    exact ⟨⟨x, hxU, rfl⟩,
      (compatibility_iff_zero U D f A hA hxU).mp hxF⟩
  · rintro ⟨⟨x, hxU, rfl⟩, hxZero⟩
    exact ⟨x, ⟨hxU,
      (compatibility_iff_zero U D f A hA hxU).mpr hxZero⟩, rfl⟩

/-- One exact straightening simultaneously straightens all
    compatibility levels, not just the zero level. -/
theorem image_compatibilityLevel
    (U : Set E) (D : E → V) (f : E → V) (A : E → E)
    (hA : ∀ x ∈ U, D (A x) = D x - f x)
    (b : V) :
    A '' {x | x ∈ U ∧ D x - f x = b} =
      (A '' U) ∩ {y | D y = b} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxU, hxF⟩, rfl⟩
    exact ⟨⟨x, hxU, rfl⟩, (hA x hxU).trans hxF⟩
  · rintro ⟨⟨x, hxU, rfl⟩, hy⟩
    exact ⟨x, ⟨hxU, (hA x hxU).symm.trans hy⟩, rfl⟩

end Compatibility

section EndpointReplacement

variable {E V : Type*} [AddCommGroup E] [AddCommGroup V]

/-- Replace an endpoint coordinate `D x` with `g (D x)` using a right
    inverse `Q`. This is an exact algebraic model for the elementary
    endpoint-coupling corollary in the paper. -/
def endpointReplacement
    (D : E →+ V) (Q : V →+ E) (g : V ≃+ V) (x : E) : E :=
  x + Q (g (D x) - D x)

/-- The endpoint coordinate of an endpoint replacement. -/
theorem endpointReplacement_coordinate
    (D : E →+ V) (Q : V →+ E)
    (hQ : ∀ v : V, D (Q v) = v)
    (g : V ≃+ V) (x : E) :
    D (endpointReplacement D Q g x) = g (D x) := by
  calc
    D (endpointReplacement D Q g x) =
        D x + D (Q (g (D x) - D x)) := by
          simp [endpointReplacement]
    _ = D x + (g (D x) - D x) := by rw [hQ]
    _ = g (D x) := by abel

/-- The endpoint replacement admits a two-sided inverse obtained by
    replacing `g` with `g.symm`. -/
theorem endpointReplacement_left_inverse
    (D : E →+ V) (Q : V →+ E)
    (hQ : ∀ v : V, D (Q v) = v)
    (g : V ≃+ V) (x : E) :
    endpointReplacement D Q g.symm
      (endpointReplacement D Q g x) = x := by
  have hc := endpointReplacement_coordinate D Q hQ g x
  change endpointReplacement D Q g x +
    Q (g.symm (D (endpointReplacement D Q g x)) -
      D (endpointReplacement D Q g x)) = x
  rw [hc, g.symm_apply_apply]
  simp only [endpointReplacement, map_sub]
  abel

/-- An explicit equivalence, not just the existence of an inverse. -/
def endpointReplacementEquiv
    (D : E →+ V) (Q : V →+ E)
    (hQ : ∀ v : V, D (Q v) = v)
    (g : V ≃+ V) : E ≃ E where
  toFun := endpointReplacement D Q g
  invFun := endpointReplacement D Q g.symm
  left_inv := endpointReplacement_left_inverse D Q hQ g
  right_inv := by
    intro x
    simpa using (endpointReplacement_left_inverse D Q hQ g.symm x)

end EndpointReplacement

end GlobalRegularization
