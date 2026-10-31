import GlobalRegularization.LocalC1Approximation
import GlobalRegularization.LocallyVanishingSeries

/-! The already constructed local `C¹` approximants give the vanishing
coefficient families required by the shell-series convergence theorem. -/

namespace GlobalRegularization

open Set Metric

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem LocalC1Approximation.locallyVanishing_values
    {U : Set E} {f : E → B} {fm : ℕ → E → B} (h : LocalC1Approximation U f fm) :
    LocallyVanishing U (fun n x => f x - fm n x) := by
  intro x hx η hη
  obtain ⟨r, hr, hball, N, hN⟩ := h x hx η hη
  refine ⟨r, hr, hball, N, ?_⟩
  intro n hn y hy
  have ht := (hN n hn y hy).le
  rw [norm_sub_rev]
  linarith [norm_nonneg (fderiv ℝ (fm n) y - fderiv ℝ f y)]

theorem LocalC1Approximation.locallyVanishing_derivatives
    {U : Set E} {f : E → B} {fm : ℕ → E → B} (h : LocalC1Approximation U f fm) :
    LocallyVanishing U (fun n x => fderiv ℝ f x - fderiv ℝ (fm n) x) := by
  intro x hx η hη
  obtain ⟨r, hr, hball, N, hN⟩ := h x hx η hη
  refine ⟨r, hr, hball, N, ?_⟩
  intro n hn y hy
  have ht := (hN n hn y hy).le
  rw [norm_sub_rev]
  linarith [norm_nonneg (fm n y - f y)]

end GlobalRegularization
