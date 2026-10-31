import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Positive shrinking widths below an arbitrary positive envelope.
This is the width selection used in the analytic construction. -/

namespace GlobalRegularization

noncomputable section

def shrinkingWidths (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0 / 2
  | n + 1 => min (u (n + 1) / 2) (shrinkingWidths u n / 4)

theorem shrinkingWidths_pos (u : ℕ → ℝ) (hu : ∀ n, 0 < u n) :
    ∀ n, 0 < shrinkingWidths u n := by
  intro n
  induction n with
  | zero => exact div_pos (hu 0) (by norm_num)
  | succ n ih => exact lt_min (div_pos (hu (n + 1)) (by norm_num)) (div_pos ih (by norm_num))

theorem shrinkingWidths_le_half (u : ℕ → ℝ) (n : ℕ) :
    shrinkingWidths u n ≤ u n / 2 := by
  cases n with
  | zero => rfl
  | succ n => exact min_le_left _ _

theorem shrinkingWidths_lt (u : ℕ → ℝ) (hu : ∀ n, 0 < u n) (n : ℕ) :
    shrinkingWidths u n < u n := by
  have hs := shrinkingWidths_le_half u n
  have hp := hu n
  linarith

theorem shrinkingWidths_step (u : ℕ → ℝ) (n : ℕ) :
    shrinkingWidths u (n + 1) ≤ shrinkingWidths u n / 4 :=
  min_le_right _ _

end

end GlobalRegularization
