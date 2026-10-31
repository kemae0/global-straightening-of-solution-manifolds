import GlobalRegularization.ShellCoordinate
import GlobalRegularization.ShellTelescoping

/-! Invertibility of the derivative of the actual shell coordinate. The
triangular operator decomposition is derived by finite telescoping and
passage to the operator-norm limit. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem shellCoordinateDerivative_isUnit
    {U : Set (C1History h B)}
    {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (hann : ∀ i j, i ≤ j → ∀ x ∈ U,
      (fderiv ℝ (fm i) x).comp (terminalCorrection h B (δ j) (hδ j)) = 0)
    {x : C1History h B} (hx : x ∈ U) :
    IsUnit (shellCoordinateDerivative h B δ hδ f fm x) := by
  let Q := fun i => terminalCorrection h B (δ i) (hδ i)
  let L := fun i => fderiv ℝ (fm i) x
  let Lf := fderiv ℝ f x
  let K : C1History h B →L[ℝ] C1History h B := -(Q 0).comp Lf +
    ∑' i, (Q i - Q (i + 1)).comp (Lf - L i)
  have hcoeff := happrox.locallyVanishing_derivatives.tendsto_zero hx
  have hL : Tendsto L atTop (𝓝 Lf) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Lf) atTop (𝓝 Lf)).sub hcoeff
    simpa only [sub_sub_cancel, sub_zero, L, Lf] using ht
  have hs : Summable (fun i => (Q i - Q (i + 1)).comp (Lf - L i)) := by
    exact summable_linear_series_of_locally_vanishing _ (4 * C) (by positivity)
      (terminalShell_operator_max_bound h B δ hδ hstep C hC.le hQ) _
      happrox.locallyVanishing_derivatives hx
  have hK : Tendsto (shellOperatorPartial Q Lf L) atTop (𝓝 K) :=
    tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat
  have htri := triangularPartial_tendsto_of_shell Q Lf L C hC.le hQ hL K hK
  have hu := isUnit_one_add_triangular_limit Q (triangularDifferences L)
    (triangularDifferences_annihilation Q L (fun i j hij => hann i j hij x hx)) K htri
  have heq : shellCoordinateDerivative h B δ hδ f fm x = 1 + K := by
    change (1 : C1History h B →L[ℝ] C1History h B) - (Q 0).comp Lf +
      (∑' i, (Q i - Q (i + 1)).comp (Lf - L i)) = 1 + K
    dsimp only [K]
    abel
  rw [heq]
  exact hu

theorem shellCoordinate_invertible_derivative
    {U : Set (C1History h B)} (hU : IsOpen U)
    {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (hf : ContDiffOn ℝ 1 f U) (hfm : ∀ i, ContDiff ℝ 1 (fm i))
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (hann : ∀ i j, i ≤ j → ∀ x ∈ U,
      (fderiv ℝ (fm i) x).comp (terminalCorrection h B (δ j) (hδ j)) = 0) :
    ∀ x ∈ U, ∃ T : C1History h B ≃L[ℝ] C1History h B,
      HasFDerivAt (shellCoordinate h B δ hδ f fm) (T : C1History h B →L[ℝ] C1History h B) x := by
  intro x hx
  have hu := shellCoordinateDerivative_isUnit h B happrox δ hδ hstep C hC hQ hann hx
  refine ⟨ContinuousLinearEquiv.ofUnit hu.unit, ?_⟩
  have heq : (ContinuousLinearEquiv.ofUnit hu.unit : C1History h B →L[ℝ] C1History h B) =
      shellCoordinateDerivative h B δ hδ f fm x := hu.unit_spec
  rw [heq]
  exact (shellCoordinate_C1 h B hU hf hfm happrox δ hδ hstep C hC hQ).2 x hx

end

end GlobalRegularization
