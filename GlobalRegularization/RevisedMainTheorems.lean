import GlobalRegularization.FiniteFullTheorem
import GlobalRegularization.LocalizedIsotopy
import GlobalRegularization.PrincipalApplications

/-! The revised principal statement: spectrum and a single positive
displacement constant shared by every affine slice in [0,1]. -/

namespace GlobalRegularization

open Set Metric
open scoped NNReal

noncomputable section

theorem LocalizedHistoryStraightening.positive_uniform_affine_bound
    (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {U : Set (C1History h B)} {f : C1History h B → B} {τ ε : ℝ}
    (chart : LocalizedHistoryStraightening h B U f τ ε) (hε : 0 < ε) :
    ∃ c ∈ Ioo (0 : ℝ) ε, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ U,
      ‖historyInclusion h B (affineHomotopy chart.forward s x - x)‖ ≤ c := by
  obtain ⟨b, hb, hbound⟩ := chart.uniform_small
  let c := (max 0 b + ε) / 2
  have hbε : max 0 b < ε := max_lt hε hb
  have hbc : max 0 b ≤ c := by dsimp only [c]; linarith
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · dsimp only [c]; linarith [le_max_left (0 : ℝ) b]
  · dsimp only [c]; linarith
  · intro s hs x hx
    simp only [affineHomotopy, add_sub_cancel_left, map_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact ((mul_le_mul_of_nonneg_left ((hbound x hx).trans (le_max_right _ _)) hs.1).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 (le_max_left (0 : ℝ) b))).trans hbc

theorem property_e_revised_main
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ) [NeZero n]
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ))
    (he : HasExtendedDerivative U (historyInclusion h (Fin n → ℝ)) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      chart.HasLocalizedAffineIsotopy h (Fin n → ℝ) ∧
      (∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1}) ∧
      (∃ c ∈ Ioo (0 : ℝ) ε, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ U,
        ‖historyInclusion h (Fin n → ℝ) (affineHomotopy chart.forward s x - x)‖ ≤ c) ∧
      chart.forward '' solutionManifold U (endpointDerivative h (Fin n → ℝ)) f =
        chart.target ∩ zeroHyperplane (endpointDerivative h (Fin n → ℝ)) := by
  obtain ⟨chart, hi, hspec⟩ := property_e_full_straightening h hh n U hU f he τ ε hτ hε
  refine ⟨chart, chart.localized_isotopy_of_affine h (Fin n → ℝ) hε hi, hspec,
    chart.positive_uniform_affine_bound h (Fin n → ℝ) hε, ?_⟩
  have himage : chart.forward '' U = chart.target := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩; exact chart.forward_maps hx
    · intro y hy; exact ⟨chart.backward y, chart.backward_maps hy, chart.right_inverse y hy⟩
  rw [← himage]
  exact c1_straightening_solution_manifold U _ f chart.toC1Straightening

theorem LocalC1Approximation.uniform_margin
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {U : Set E} {f : E → B} {fm : ℕ → E → B} (happ : LocalC1Approximation U f fm)
    {x : E} (hx : x ∈ U) (η : ℝ) (hη : 0 < η) :
    ∃ r > 0, ball x r ⊆ U ∧ ∃ N : ℕ, ∃ c < η,
      ∀ n ≥ N, ∀ y ∈ ball x r,
        ‖fm n y - f y‖ + ‖fderiv ℝ (fm n) y - fderiv ℝ f y‖ ≤ c := by
  obtain ⟨r, hr, hball, N, hN⟩ := happ x hx (η / 2) (by positivity)
  exact ⟨r, hr, hball, N, η / 2, by linarith, fun n hn y hy => (hN n hn y hy).le⟩

end

end GlobalRegularization
