import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.RingTheory.Polynomial.Bernstein
import GlobalRegularization.BernsteinOperators
import Mathlib.Tactic

/-! Exact difference-quotient derivative formula for Banach-valued
Bernstein curves. No differentiability assumption on the coefficients
and no finite-dimensional assumption on the codomain are needed. -/

namespace GlobalRegularization

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem sum_discrete_parts (w : ℕ → ℝ) (c : ℕ → B) (n : ℕ) :
    (∑ i ∈ Finset.range n, (w i - w (i + 1)) • c (i + 1)) =
      (∑ i ∈ Finset.range n, w i • (c (i + 1) - c i)) + w 0 • c 0 - w n • c n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp only [sub_smul, smul_sub]
      abel

def bernsteinCurve (n : ℕ) (c : ℕ → B) (t : ℝ) : B :=
  ∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval t • c k

theorem hasDerivAt_bernsteinCurve_raw (n : ℕ) (c : ℕ → B) (t : ℝ) :
    HasDerivAt (bernsteinCurve n c)
      (∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).derivative.eval t • c k) t :=
  HasDerivAt.fun_sum (fun k _hk => ((bernsteinPolynomial ℝ n k).hasDerivAt t).smul_const (c k))

theorem continuous_bernsteinCurve (n : ℕ) (c : ℕ → B) : Continuous (bernsteinCurve n c) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_bernsteinCurve_raw n c t).continuousAt)

theorem bernsteinCurve_derivative_formula (n : ℕ) (c : ℕ → B) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 2), (bernsteinPolynomial ℝ (n + 1) k).derivative.eval t • c k) =
      (n + 1 : ℝ) • bernsteinCurve n (fun k => c (k + 1) - c k) t := by
  rw [Finset.sum_range_succ']
  simp only [bernsteinPolynomial.derivative_succ, bernsteinPolynomial.derivative_zero,
    Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_natCast, mul_smul, neg_smul, ← Finset.smul_sum]
  have hparts := sum_discrete_parts
    (fun k => (bernsteinPolynomial ℝ n k).eval t) c (n + 1)
  have hz : (bernsteinPolynomial ℝ n (n + 1)).eval t = 0 := by
    rw [bernsteinPolynomial.eq_zero_of_lt ℝ (by omega), Polynomial.eval_zero]
  rw [hz, zero_smul, sub_zero] at hparts
  rw [hparts]
  simp only [bernsteinCurve, smul_add, smul_smul]
  module

theorem hasDerivAt_bernsteinCurve (n : ℕ) (c : ℕ → B) (t : ℝ) :
    HasDerivAt (bernsteinCurve (n + 1) c)
      ((n + 1 : ℝ) • bernsteinCurve n (fun k => c (k + 1) - c k) t) t := by
  have h := hasDerivAt_bernsteinCurve_raw (n + 1) c t
  rw [show n + 1 + 1 = n + 2 by omega, bernsteinCurve_derivative_formula] at h
  exact h

open scoped unitInterval Topology

def bernsteinCurveCM (n : ℕ) (c : ℕ → B) : C(I, B) :=
  ⟨fun t => bernsteinCurve n c t, (continuous_bernsteinCurve n c).comp continuous_subtype_val⟩

theorem bernsteinCurveCM_eq_synthesis (n : ℕ) (c : ℕ → B) :
    bernsteinCurveCM n c = bernsteinSynthesis B n (fun k => c k) := by
  ext t
  simp [bernsteinCurveCM, bernsteinCurve, bernsteinSynthesis_apply,
    bernstein, Finset.sum_range]

theorem bernsteinCurve_coeff_smul (n : ℕ) (c : ℕ → B) (r t : ℝ) :
    bernsteinCurve n (fun k => r • c k) t = r • bernsteinCurve n c t := by
  simp only [bernsteinCurve, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact smul_comm _ _ _

theorem norm_bernsteinCurve_le (n : ℕ) (c : ℕ → B) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ k, k ≤ n → ‖c k‖ ≤ M) (t : I) : ‖bernsteinCurve n c t‖ ≤ M := by
  have hnorm := norm_bernsteinSynthesis_le B n (fun k : Fin (n + 1) => c k)
  have hcoeff : ‖fun k : Fin (n + 1) => c k‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM).2 (fun k => hc k (by omega))
  have hpoint := (bernsteinSynthesis B n (fun k => c k)).norm_coe_le_norm t
  have heval : bernsteinCurve n c t = bernsteinSynthesis B n (fun k => c k) t :=
    congrArg (fun f : C(I, B) => f t) (bernsteinCurveCM_eq_synthesis n c)
  rw [heval]
  exact hpoint.trans (hnorm.trans hcoeff)

def bernsteinDifferenceCoefficients (n : ℕ) (c : ℕ → B) (k : ℕ) : B :=
  (n + 1 : ℝ) • (c (k + 1) - c k)

theorem hasDerivAt_bernsteinCurve_difference (n : ℕ) (c : ℕ → B) (t : ℝ) :
    HasDerivAt (bernsteinCurve (n + 1) c)
      (bernsteinCurve n (bernsteinDifferenceCoefficients n c) t) t := by
  change HasDerivAt (bernsteinCurve (n + 1) c)
    (bernsteinCurve n (fun k => (n + 1 : ℝ) • (c (k + 1) - c k)) t) t
  rw [bernsteinCurve_coeff_smul]
  exact hasDerivAt_bernsteinCurve n c t

/-- This isolates precisely the coefficient convergence still needed to
deduce `C¹` approximation of histories from the Bernstein construction. -/
theorem bernsteinCurve_derivatives_tendsto
    (g : C(I, B)) (c : ℕ → ℕ → B)
    (hcoeff : Filter.Tendsto
      (fun n => ‖(fun k : Fin (n + 1) => bernsteinDifferenceCoefficients n (c n) k) -
        bernsteinSamples B n g‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => bernsteinCurveCM n (bernsteinDifferenceCoefficients n (c n)))
      Filter.atTop (nhds g) := by
  simpa only [bernsteinCurveCM_eq_synthesis] using
    bernsteinSynthesis_moving_coefficients B g
      (fun n k => bernsteinDifferenceCoefficients n (c n) k) hcoeff

end

end GlobalRegularization
