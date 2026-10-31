import GlobalRegularization.VectorMarkovOperators
import GlobalRegularization.FiniteOutputLimits

/-! The adjoint approximation for actual finite-state history functionals,
derived componentwise from the constructed Markov and cutoff operators. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section

theorem matrixHistoryFunctional_adapted_adjoint
    (h : ℝ≥0) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ ρ : Fin n → Fin n → Measure (HistoryInterval h))
    [∀ i j, IsFiniteMeasure (μ i j)] [∀ i j, IsFiniteMeasure (ρ i j)]
    (hrep : ∀ x i, L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
      ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
        ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ρ i j))
    (ν : Measure (HistoryInterval h)) [IsFiniteMeasure ν] [ν.WeaklyRegular]
    (hfull : ∀ U : Set (HistoryInterval h), IsOpen U → U.Nonempty → 0 < ν U)
    (hμac : ∀ i j, μ i j ≪ ν) (hρac : ∀ i j, ρ i j ≪ ν)
    (hμatom : ∀ i j, μ i j {historyRight h} = 0)
    (hρatom : ∀ i j, ρ i j {historyRight h} = 0) :
    Tendsto (fun m => L.comp (adaptedHistoryOperator h (Fin n → ℝ) ν m -
      ContinuousLinearMap.id ℝ (C1History h (Fin n → ℝ)))) atTop (𝓝 0) := by
  let D := fun j : Fin n => (continuousVectorComponent n j).comp (historyDerivative h (Fin n → ℝ))
  let T := fun m => adaptedDerivativeOperator h ℝ ν m - ContinuousLinearMap.id ℝ (ContinuousHistory h ℝ)
  let M := fun i j => continuousIntegralFunctional (HistoryInterval h) (μ i j)
  let N := fun i j => continuousIntegralFunctional (HistoryInterval h) (ρ i j)
  have heq (m : ℕ) (i : Fin n) :
      (ContinuousLinearMap.proj i).comp (L.comp (adaptedHistoryOperator h (Fin n → ℝ) ν m -
        ContinuousLinearMap.id ℝ (C1History h (Fin n → ℝ)))) =
      ∑ j : Fin n, (((M i j).comp (T m)).comp (D j) - ((N i j).comp (T m)).comp (D j)) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub, ContinuousLinearMap.sum_apply]
    change L (adaptedHistoryOperator h (Fin n → ℝ) ν m x) i - L x i = _
    rw [hrep, hrep, adaptedHistoryOperator, reconstructHistoryOperator_apply,
      historyReconstruct_left, historyReconstruct_derivative, add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hcomp := adaptedDerivativeOperator_component h ν n j m (historyDerivative h (Fin n → ℝ) x)
    change continuousVectorComponent n j (adaptedDerivativeOperator h (Fin n → ℝ) ν m
      (historyDerivative h (Fin n → ℝ) x)) = adaptedDerivativeOperator h ℝ ν m (D j x) at hcomp
    have ht : ((M i j) (continuousVectorComponent n j (adaptedDerivativeOperator h (Fin n → ℝ) ν m
      (historyDerivative h (Fin n → ℝ) x))) - (N i j) (continuousVectorComponent n j
      (adaptedDerivativeOperator h (Fin n → ℝ) ν m (historyDerivative h (Fin n → ℝ) x)))) -
      ((M i j) (D j x) - (N i j) (D j x)) =
      (M i j) (T m (D j x)) - (N i j) (T m (D j x)) := by
      rw [hcomp]
      simp only [T, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
      abel
    simpa only [M, N, D, continuousIntegralFunctional_apply, ContinuousLinearMap.comp_apply,
      continuousVectorComponent_apply] using ht
  apply finiteOutputCLM_tendsto_zero n
  intro i
  have ht (j : Fin n) := (tendsto_clm_comp_const_zero _
    (adaptedDerivativeOperator_measure_adjoint h ν hfull (μ i j) (hμac i j) (hμatom i j)) (D j)).sub
    (tendsto_clm_comp_const_zero _
      (adaptedDerivativeOperator_measure_adjoint h ν hfull (ρ i j) (hρac i j) (hρatom i j)) (D j))
  simpa only [heq, sub_self, Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun j hj => ht j)

end

end GlobalRegularization
