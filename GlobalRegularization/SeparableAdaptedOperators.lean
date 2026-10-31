import GlobalRegularization.MatrixAdaptedAdjoint
import GlobalRegularization.AtomFreeRepresentation
import GlobalRegularization.IntervalReferenceMeasure
import GlobalRegularization.HistorySeparable
import GlobalRegularization.CommonDominatingMeasure
import GlobalRegularization.DenseDualApproximation

/-! A common adapted approximation for a separable family of history
functionals. Adjoint convergence extends from a countable dense family
by uniform operator bounds. Empty families are included. -/

namespace GlobalRegularization

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology

noncomputable section

theorem adaptedTerminalWidth_antitone (h : ℝ≥0) : Antitone (adaptedTerminalWidth h) := by
  intro m n hmn
  apply div_le_div_of_nonneg_left h.coe_nonneg (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 2

theorem exists_adapted_operators_for_separable_family
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (S : Set (C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) (hsep : IsSeparable S)
    (hzero : ∀ L ∈ S, Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ)
      (adaptedTerminalWidth h m) (adaptedTerminalWidth_pos h hh m))) atTop (𝓝 0)) :
    ∃ P : ℕ → C1History h (Fin n → ℝ) →L[ℝ] C1History h (Fin n → ℝ),
    ∃ C : ℝ, 0 < C ∧ (∀ m, ‖P m‖ ≤ C) ∧
      (∀ x, Tendsto (fun m => P m x) atTop (𝓝 x)) ∧
      (∀ m, FiniteDimensional ℝ (LinearMap.range (P m))) ∧
      (∀ L ∈ S, Tendsto (fun m => L.comp (P m -
        ContinuousLinearMap.id ℝ (C1History h (Fin n → ℝ)))) atTop (𝓝 0)) ∧
      ∀ m δ (hδ : 0 < δ), δ / 2 < adaptedTerminalWidth h m →
        (P m).comp (terminalCorrection h (Fin n → ℝ) δ hδ) = 0 := by
  obtain ⟨s, hsS, hscount, hsclosure⟩ := hsep.exists_countable_dense_subset
  letI := hscount.to_subtype
  have hrep (k : s) := historyFunctional_atomfree_representation h hh n k.val
    (hzero k.val (hsS k.property))
  choose A μ ρ hμ hρ hμatom hρatom hrep using hrep
  letI := hμ
  letI := hρ
  let measures : (s × Fin n × Fin n × Bool) → Measure (HistoryInterval h) :=
    fun k => if k.2.2.2 then μ k.1 k.2.1 k.2.2.1 else ρ k.1 k.2.1 k.2.2.1
  have hfinite (k : s × Fin n × Fin n × Bool) : IsFiniteMeasure (measures k) := by
    dsimp only [measures]
    split <;> infer_instance
  letI := hfinite
  have hatom (k : s × Fin n × Fin n × Bool) : measures k {historyRight h} = 0 := by
    dsimp only [measures]
    split
    · exact hμatom _ _ _
    · exact hρatom _ _ _
  obtain ⟨ν, hν, hβν, hdom, hνatom, hpos⟩ := exists_common_finite_dominating_measure measures
    (historyLebesgue h) (historyRight h) hatom (historyLebesgue_singleton h _)
  letI := hν
  have hfull : ∀ U : Set (HistoryInterval h), IsOpen U → U.Nonempty → 0 < ν U :=
    fun U hU hne => hpos U (historyLebesgue_full_support h hh U hU hne)
  have hμac (k : s) (i j : Fin n) : μ k i j ≪ ν := by
    simpa only [measures, Bool.true_eq_false, if_true] using hdom (k, i, j, true)
  have hρac (k : s) (i j : Fin n) : ρ k i j ≪ ν := by
    simpa only [measures, Bool.false_eq_true, if_false] using hdom (k, i, j, false)
  let P := adaptedHistoryOperator h (Fin n → ℝ) ν
  let C := max 1 ‖(historyCoordinates h (Fin n → ℝ)).symm.toContinuousLinearMap‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hP : ∀ m, ‖P m‖ ≤ C := fun m =>
    (adaptedHistoryOperator_uniform_bound h (Fin n → ℝ) ν m).trans (le_max_right _ _)
  refine ⟨P, C, hC, hP, adaptedHistoryOperator_strong h (Fin n → ℝ) ν hfull,
    adaptedHistoryOperator_finite_range h (Fin n → ℝ) ν, ?_,
    adaptedHistoryOperator_annihilates_terminal h (Fin n → ℝ) ν⟩
  intro L hLS
  apply derivativeApproximation_of_mem_closure P C hC.le hP s _ (hsclosure hLS)
  intro M hMs
  let k : s := ⟨M, hMs⟩
  exact matrixHistoryFunctional_adapted_adjoint h n M (A k) (μ k) (ρ k) (hrep k) ν hfull
    (hμac k) (hρac k) (hμatom k) (hρatom k)

end

end GlobalRegularization
