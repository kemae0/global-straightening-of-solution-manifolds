import GlobalRegularization.MarkovApproximation

/-! Positivity of the actual finite-rank Markov approximants. -/

namespace GlobalRegularization

open Set MeasureTheory

noncomputable section

theorem finiteMarkovOperator_nonneg
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1)
    (g : C(X, ℝ)) (hg : ∀ x, 0 ≤ g x) (t : X) :
    0 ≤ finiteMarkovOperator ℝ μ ψ hψ hsum g t := by
  rw [finiteMarkovOperator_apply]
  apply Finset.sum_nonneg
  intro j _
  change 0 ≤ ψ j t * ((∫ s, ψ j s ∂μ)⁻¹ * ∫ s, ψ j s * g s ∂μ)
  exact mul_nonneg (hψ j t) (mul_nonneg (inv_nonneg.mpr (integral_nonneg (hψ j)))
    (integral_nonneg (fun s => mul_nonneg (hψ j s) (hg s))))

theorem markovApproximation_nonneg
    (X : Type*) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (m : ℕ) (g : C(X, ℝ)) (hg : ∀ x, 0 ≤ g x) (t : X) :
    0 ≤ markovApproximation ℝ X μ m g t :=
  finiteMarkovOperator_nonneg μ _ _ _ g hg t

end

end GlobalRegularization
