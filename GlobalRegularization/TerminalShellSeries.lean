import GlobalRegularization.TerminalShells
import GlobalRegularization.C1LinearSeries
import GlobalRegularization.ApproximationVanishing

/-! Convergence and the exact derivative of the manuscript's terminal
shell error series, instantiated on genuine continuously differentiable
histories. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem terminalShell_max_bound
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 ≤ C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C) :
    HasMaxFiniteSumBound (terminalShell h B δ hδ) (4 * C) := by
  intro s a M hM ha
  exact norm_terminalShell_sum_le h B δ hδ hstep C hC hQ s a M hM ha

theorem terminalShell_operator_max_bound
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 ≤ C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C) :
    HasMaxFiniteSumBound
      (fun i => ContinuousLinearMap.compL ℝ D B (C1History h B) (terminalShell h B δ hδ i))
      (4 * C) := by
  intro s L M hM hL
  exact norm_terminalShell_operator_sum_le h B δ hδ hstep C hC hQ s L M hM hL

def terminalShellError (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B) :
    C1History h B := ∑' i, terminalShell h B δ hδ i (f x - fm i x)

theorem terminalShellError_summable
    {U : Set (C1History h B)} {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    {x : C1History h B} (hx : x ∈ U) :
    Summable (fun i => terminalShell h B δ hδ i (f x - fm i x)) := by
  exact summable_linear_series_of_locally_vanishing _ (4 * C) (by positivity)
    (terminalShell_max_bound h B δ hδ hstep C hC.le hQ) _
    happrox.locallyVanishing_values hx

theorem terminalShellError_C1
    {U : Set (C1History h B)} (hU : IsOpen U)
    {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (hf : ContDiffOn ℝ 1 f U) (hfm : ∀ i, ContDiff ℝ 1 (fm i))
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C) :
    ContDiffOn ℝ 1 (terminalShellError h B δ hδ f fm) U ∧
      ∀ x ∈ U, HasFDerivAt (terminalShellError h B δ hδ f fm)
        (∑' i, (terminalShell h B δ hδ i).comp (fderiv ℝ f x - fderiv ℝ (fm i) x)) x := by
  apply C1_linear_series_of_locally_vanishing hU _ (4 * C) (by positivity)
    (terminalShell_max_bound h B δ hδ hstep C hC.le hQ)
    (terminalShell_operator_max_bound h B δ hδ hstep C hC.le hQ)
    (fun i x => f x - fm i x) (fun i x => fderiv ℝ f x - fderiv ℝ (fm i) x)
    happrox.locallyVanishing_values happrox.locallyVanishing_derivatives
  · intro i x hx
    exact ((hf.differentiableOn le_rfl x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.sub
      ((hfm i).differentiable le_rfl x).hasFDerivAt
  · intro i
    exact (hf.continuousOn_fderiv_of_isOpen hU le_rfl).sub
      ((hfm i).continuous_fderiv le_rfl).continuousOn

end

end GlobalRegularization
