import GlobalRegularization.AdaptedHistoryOperators
import GlobalRegularization.VectorRieszRepresentation

/-! Component projections commute with the actual averaging and terminal
cutoff operators, as required by the matrix-valued Riesz representation. -/

namespace GlobalRegularization

open Set MeasureTheory
open scoped NNReal

noncomputable section

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem weightedAverage_component (n : ℕ) (j : Fin n) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 ≤ ψ x) (g : C(X, Fin n → ℝ)) :
    weightedAverage μ (Fin n → ℝ) ψ hψ g j =
      weightedAverage μ ℝ ψ hψ (continuousVectorComponent n j g) := by
  change ((∫ x, ψ x ∂μ)⁻¹ • ∫ x, ψ x • g x ∂μ) j =
    (∫ x, ψ x ∂μ)⁻¹ • ∫ x, ψ x • g x j ∂μ
  have hi := (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm
    (continuous_compact_integrable μ (Fin n → ℝ) (ψ • g))
  change (∫ x, ψ x • g x j ∂μ) = (∫ x, ψ x • g x ∂μ) j at hi
  simp only [Pi.smul_apply, hi]

theorem finiteMarkovOperator_component {ι : Type*} [Fintype ι]
    (n : ℕ) (j : Fin n) (ψ : ι → C(X, ℝ))
    (hψ : ∀ i x, 0 ≤ ψ i x) (hsum : ∀ x, ∑ i, ψ i x = 1)
    (g : C(X, Fin n → ℝ)) :
    continuousVectorComponent n j (finiteMarkovOperator (Fin n → ℝ) μ ψ hψ hsum g) =
      finiteMarkovOperator ℝ μ ψ hψ hsum (continuousVectorComponent n j g) := by
  ext t
  simp only [continuousVectorComponent_apply, finiteMarkovOperator_apply, Finset.sum_apply,
    Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact weightedAverage_component μ n j (ψ i) (hψ i) g

theorem markovApproximation_component (n : ℕ) (j : Fin n)
    (m : ℕ) (g : C(X, Fin n → ℝ)) :
    continuousVectorComponent n j (markovApproximation (Fin n → ℝ) X μ m g) =
      markovApproximation ℝ X μ m (continuousVectorComponent n j g) :=
  finiteMarkovOperator_component μ n j _ _ _ g

theorem terminalHistoryCutoff_component (h : ℝ≥0) (n : ℕ) (j : Fin n)
    (σ : ℝ) (hσh : σ ≤ (h : ℝ)) (g : ContinuousHistory h (Fin n → ℝ)) :
    continuousVectorComponent n j (terminalHistoryCutoff h (Fin n → ℝ) σ hσh g) =
      terminalHistoryCutoff h ℝ σ hσh (continuousVectorComponent n j g) := rfl

theorem adaptedDerivativeOperator_component (h : ℝ≥0) (ν : Measure (HistoryInterval h))
    [IsFiniteMeasure ν] (n : ℕ) (j : Fin n) (m : ℕ) (g : ContinuousHistory h (Fin n → ℝ)) :
    continuousVectorComponent n j (adaptedDerivativeOperator h (Fin n → ℝ) ν m g) =
      adaptedDerivativeOperator h ℝ ν m (continuousVectorComponent n j g) := by
  rw [adaptedDerivativeOperator, ContinuousLinearMap.comp_apply,
    markovApproximation_component, terminalHistoryCutoff_component]
  rfl

end

end GlobalRegularization
