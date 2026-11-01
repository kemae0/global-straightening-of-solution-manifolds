import GlobalRegularization.BernsteinOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Basis.Basic

/-! Real linear independence of the actual Bernstein functions.
The polynomial induction adapts mathlib's rational-coefficient proof in
RingTheory/Polynomial/Bernstein.lean (Kim Morrison, Apache 2.0). -/

namespace GlobalRegularization

open Set Polynomial Submodule
open scoped unitInterval Polynomial

noncomputable section

theorem bernsteinPolynomial_real_independent_aux (n k : ℕ) (h : k ≤ n + 1) :
    LinearIndependent ℝ (fun j : Fin k => bernsteinPolynomial ℝ n j) := by
  induction k with
  | zero => exact linearIndependent_empty_type
  | succ k ih =>
    apply linearIndependent_fin_succ'.mpr
    refine ⟨ih (le_of_lt h), ?_⟩
    clear ih
    simp only [add_le_add_iff_right] at h
    simp only [Fin.val_last, Fin.init_def]
    dsimp
    apply notMem_span_of_apply_notMem_span_image (@Polynomial.derivative ℝ _ ^ (n - k))
    simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image _]
    intro p hp
    apply_fun Polynomial.eval (1 : ℝ)
    simp only [Module.End.pow_apply]
    suffices hz : (Polynomial.derivative^[n - k] p).eval 1 = 0 by
      rw [hz]
      exact (bernsteinPolynomial.iterate_derivative_at_1_ne_zero ℝ n k h).symm
    refine span_induction ?_ ?_ ?_ ?_ hp
    · simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      rintro ⟨j, hj⟩
      simp only
      rw [bernsteinPolynomial.iterate_derivative_at_1_eq_zero_of_lt ℝ n
        ((tsub_lt_tsub_iff_left_of_le h).mpr hj)]
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro a x _ hx; simp [hx]

def polynomialUnitIntervalL : ℝ[X] →ₗ[ℝ] C(I, ℝ) where
  toFun p := p.toContinuousMapOn I
  map_add' p q := by ext x; simp
  map_smul' a p := by ext x; simp

theorem polynomialUnitIntervalL_injective : Function.Injective polynomialUnitIntervalL := by
  intro p q hpq
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num)).mono
  intro x hx
  exact congrArg (fun f : C(I, ℝ) => f ⟨x, hx⟩) hpq

theorem bernstein_real_independent (n : ℕ) :
    LinearIndependent ℝ (fun j : Fin (n + 1) => bernstein n j) := by
  exact (bernsteinPolynomial_real_independent_aux n (n + 1) le_rfl).map'
    polynomialUnitIntervalL (LinearMap.ker_eq_bot.mpr polynomialUnitIntervalL_injective)

end

end GlobalRegularization
