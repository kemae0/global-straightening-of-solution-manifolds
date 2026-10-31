import Mathlib.Tactic

/-!
# Triangular observation argument

The genuinely algebraic part of the injectivity proof in Section 2 of
"On global regularization of solution manifolds".

This works for arbitrary observation spaces and arbitrary nonlinear
approximation maps. No topology, compactness or finite dimensionality
is used. It is *not* the analytic theorem constructing the coordinate map.


-/

namespace GlobalRegularization

universe u v w

section TriangularInjectivity

variable {E : Type u} {Z : Type v} {W : Type w}
variable [AddCommGroup Z]

/-- An abstract triangular observation identity.  The correction at level
`j` is a sum of functions of strictly earlier approximations. -/
def HasTriangularObservations
    (A : E → E) (O : ℕ → E → Z) (f : ℕ → E → W)
    (c : ℕ → ℕ → W → Z) : Prop :=
  ∀ j x, O j (A x) = O j x +
    (Finset.range j).sum (fun i => c j i (f i x))

/-- The nested-observation induction used to establish global injectivity.
This isolates the argument that does not depend on analytic approximations. -/
theorem triangular_injective
    (A : E → E) (O : ℕ → E → Z) (f : ℕ → E → W)
    (c : ℕ → ℕ → W → Z)
    (htri : HasTriangularObservations A O f c)
    (hfactor : ∀ (i : ℕ) (x y : E), O i x = O i y → f i x = f i y)
    (hseparate : ∀ x y : E, (∀ j, O j x = O j y) → x = y) :
    Function.Injective A := by
  intro x y hA
  apply hseparate x y
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      have hsum :
          (Finset.range j).sum (fun i => c j i (f i x)) =
          (Finset.range j).sum (fun i => c j i (f i y)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        exact congrArg (c j i) (hfactor i x y (ih i hij))
      have hcoord : O j (A x) = O j (A y) := congrArg (O j) hA
      rw [htri j x, htri j y, hsum] at hcoord
      exact add_right_cancel hcoord

end TriangularInjectivity

/-- The observation spaces may vary with the index, and the triangular
identity is required only on the actual domain. -/
theorem triangular_injective_on
    {E W : Type*} {Z : ℕ → Type*} [∀ j, AddCommGroup (Z j)]
    (U : Set E) (A : E → E) (O : ∀ j, E → Z j) (f : ℕ → E → W)
    (c : ∀ j, ℕ → W → Z j)
    (htri : ∀ j x, x ∈ U →
      O j (A x) = O j x + ∑ i ∈ Finset.range j, c j i (f i x))
    (hfactor : ∀ i x y, x ∈ U → y ∈ U → O i x = O i y → f i x = f i y)
    (hseparate : ∀ x y, x ∈ U → y ∈ U → (∀ j, O j x = O j y) → x = y) :
    Set.InjOn A U := by
  intro x hx y hy hxy
  apply hseparate x y hx hy
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      have hsum : (∑ i ∈ Finset.range j, c j i (f i x)) =
          ∑ i ∈ Finset.range j, c j i (f i y) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (c j i)
          (hfactor i x y hx hy (ih i (Finset.mem_range.mp hi)))
      have hcoord := congrArg (O j) hxy
      rw [htri j x hx, htri j y hy, hsum] at hcoord
      exact add_right_cancel hcoord

end GlobalRegularization
