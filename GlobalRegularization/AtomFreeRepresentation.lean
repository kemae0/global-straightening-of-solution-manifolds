import GlobalRegularization.MatrixTerminalAtom
import GlobalRegularization.AtomRemoval
import GlobalRegularization.AdaptedHistoryOperators

/-! The endpoint-limit hypothesis gives positive atom-free representing
measures, by cancelling the equal endpoint atoms of a Riesz decomposition. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section

theorem historyFunctional_atomfree_representation
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hzero : Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ)
      (adaptedTerminalWidth h m) (adaptedTerminalWidth_pos h hh m))) atTop (𝓝 0)) :
    ∃ A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
    ∃ μ ν : Fin n → Fin n → Measure (HistoryInterval h),
      (∀ i j, IsFiniteMeasure (μ i j)) ∧ (∀ i j, IsFiniteMeasure (ν i j)) ∧
      (∀ i j, μ i j {historyRight h} = 0) ∧ (∀ i j, ν i j {historyRight h} = 0) ∧
      ∀ x i, L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
        ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
          ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ν i j) := by
  obtain ⟨A, μ, ν, hμ, hν, hrep⟩ := historyFunctional_matrix_representation h n L
  letI := hμ
  letI := hν
  have hatom := (matrixHistoryFunctional_terminal_zero_iff h hh n L A μ ν hrep
    (adaptedTerminalWidth h) (adaptedTerminalWidth_pos h hh) (adaptedTerminalWidth_tendsto h)).mp hzero
  refine ⟨A, fun i j => removeMeasureAtom (μ i j) (historyRight h),
    fun i j => removeMeasureAtom (ν i j) (historyRight h),
    fun i j => inferInstance, fun i j => inferInstance,
    fun i j => removeMeasureAtom_singleton _ _, fun i j => removeMeasureAtom_singleton _ _, ?_⟩
  intro x i
  rw [hrep]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_difference_remove_atom (μ i j) (ν i j) (historyRight h)
    (sub_eq_zero.mp (hatom i j)) (continuousVectorComponent n j (historyDerivative h (Fin n → ℝ) x))

end

end GlobalRegularization
