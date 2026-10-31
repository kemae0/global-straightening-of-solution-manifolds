import GlobalRegularization.ShellGeometry
import GlobalRegularization.BoundedOverlap

/-! The manuscript's finite shell-sum estimates, for actual terminal
corrections and their operator-valued coefficients. -/

namespace GlobalRegularization

open scoped NNReal

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def terminalShell (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (i : ℕ) : B →L[ℝ] C1History h B :=
  terminalCorrection h B (δ i) (hδ i) - terminalCorrection h B (δ (i + 1)) (hδ (i + 1))

theorem terminalShell_zero_of_inactive
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (i : ℕ) (a : B) (t : HistoryInterval h)
    (hi : ¬shellActive δ hδ i t) :
    historyInclusion h B (terminalShell h B δ hδ i a) t = 0 ∧
      historyDerivative h B (terminalShell h B δ hδ i a) t = 0 := by
  have hv := not_ne_iff.mp (not_or.mp hi).1
  have hd := not_ne_iff.mp (not_or.mp hi).2
  constructor
  · change terminalProfile (δ i) (hδ i) t • a - terminalProfile (δ (i + 1)) (hδ (i + 1)) t • a = 0
    rw [hv, sub_self]
  · change deriv (terminalProfile (δ i) (hδ i)) t • a -
      deriv (terminalProfile (δ (i + 1)) (hδ (i + 1))) t • a = 0
    rw [hd, sub_self]

theorem norm_terminalShell_le
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (C : ℝ)
    (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C) (i : ℕ) :
    ‖terminalShell h B δ hδ i‖ ≤ 2 * C := by
  exact (norm_sub_le _ _).trans (by linarith [hQ i, hQ (i + 1)])

theorem norm_terminalShell_sum_le
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 ≤ C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (s : Finset ℕ) (a : ℕ → B) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ i ∈ s, ‖a i‖ ≤ M) :
    ‖∑ i ∈ s, terminalShell h B δ hδ i (a i)‖ ≤ 4 * C * M := by
  classical
  have hbound : ∀ i ∈ s, ‖terminalShell h B δ hδ i (a i)‖ ≤ 2 * C * M := by
    intro i hi
    calc
      _ ≤ ‖terminalShell h B δ hδ i‖ * ‖a i‖ := (terminalShell h B δ hδ i).le_opNorm _
      _ ≤ (2 * C) * ‖a i‖ := mul_le_mul_of_nonneg_right (norm_terminalShell_le h B δ hδ C hQ i) (norm_nonneg _)
      _ ≤ 2 * C * M := mul_le_mul_of_nonneg_left (ha i hi) (by positivity)
  have hcard : ∀ t : HistoryInterval h,
      (boundedActiveIndices s (fun i t => shellActive δ hδ i (t : ℝ)) t).card ≤ 2 := by
    intro t
    simpa only [boundedActiveIndices] using shellActive_card_le_two δ hδ hstep s t
  have H := norm_history_sum_le_bounded_overlap h B s
    (fun i => terminalShell h B δ hδ i (a i)) (fun i t => shellActive δ hδ i (t : ℝ))
    2 (2 * C * M) (by positivity) hcard
    (fun i hi t hnot => terminalShell_zero_of_inactive h B δ hδ i (a i) t hnot) hbound
  calc
    _ ≤ (2 : ℝ) * (2 * C * M) := H
    _ = 4 * C * M := by ring

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem norm_terminalShell_operator_sum_le
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 ≤ C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (s : Finset ℕ) (L : ℕ → D →L[ℝ] B) (M : ℝ) (hM : 0 ≤ M) (hL : ∀ i ∈ s, ‖L i‖ ≤ M) :
    ‖∑ i ∈ s, (terminalShell h B δ hδ i).comp (L i)‖ ≤ 4 * C * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hbound : ∀ i ∈ s, ‖L i x‖ ≤ M * ‖x‖ := by
    intro i hi
    exact ((L i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hL i hi) (norm_nonneg x))
  have H := norm_terminalShell_sum_le h B δ hδ hstep C hC hQ s (fun i => L i x)
    (M * ‖x‖) (by positivity) hbound
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, mul_assoc] using H

end

end GlobalRegularization
