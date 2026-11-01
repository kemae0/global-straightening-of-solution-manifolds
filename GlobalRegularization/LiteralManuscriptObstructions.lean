import GlobalRegularization.HilbertExistence
import GlobalRegularization.IntervalReferenceMeasure
import GlobalRegularization.EndpointObstruction

/-! Counterexamples to literal manuscript assertions. These are proofs of
their negations; the false assertions are never installed as axioms. -/

namespace GlobalRegularization

open Set MeasureTheory
open scoped NNReal

noncomputable section

abbrev ZeroHilbertState := EuclideanSpace ℝ (Fin 0)
abbrev ZeroHilbertHistory := C1History 1 ZeroHilbertState

theorem zeroHilbert_feedback_has_property_e :
    HasExtendedDerivative (univ : Set ZeroHilbertHistory) (historyInclusion 1 ZeroHilbertState)
      (fun _ => (0 : ZeroHilbertState)) := by
  refine ⟨contDiffOn_const, fun _ => 0, ?_, ?_⟩
  · intro x _
    simp only [ContinuousLinearMap.zero_comp]
    exact (hasFDerivAt_const (0 : ZeroHilbertState) x).fderiv
  · exact continuousOn_const

theorem zeroHilbert_no_map_has_claimed_spectrum (A : ZeroHilbertHistory → ZeroHilbertHistory) :
    spectrum ℂ (RealComplexification.map (fderiv ℝ A 0)) ≠ {1} := by
  letI : Subsingleton ZeroHilbertHistory :=
    inferInstanceAs (Subsingleton (LinearMap.ker (historyDefect 1 ZeroHilbertState)))
  letI : Subsingleton (RealComplexification ZeroHilbertHistory) :=
    ⟨fun x y => RealComplexification.ext (fun _ => Subsingleton.elim _ _)⟩
  rw [spectrum.of_subsingleton]
  intro heq
  have hm : (1 : ℂ) ∈ (∅ : Set ℂ) := heq.symm ▸ mem_singleton (1 : ℂ)
  exact hm

/-- All the spatial hypotheses of the written Hilbert theorem hold here,
but its spectrum conclusion is impossible, even for arbitrary maps. -/
theorem literal_Hilbert_conclusion_false :
    ¬ ∃ chart : LocalizedHistoryStraightening 1 ZeroHilbertState univ (fun _ => 0) (1 / 2) 1,
      ∀ x ∈ (univ : Set ZeroHilbertHistory),
        spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  rintro ⟨chart, hs⟩
  exact zeroHilbert_no_map_has_claimed_spectrum chart.forward (hs 0 (mem_univ _))

/-- A genuine continuous nonnegative partition of unity for a measure
of full support can have a zero denominator, as allowed in the text. -/
theorem full_support_partition_zero_denominator :
    ∃ ψ : Bool → ContinuousHistory 1 ℝ,
      (∀ j x, 0 ≤ ψ j x) ∧ (∀ x, ∑ j, ψ j x = 1) ∧
      (∀ V : Set (HistoryInterval 1), IsOpen V → V.Nonempty → 0 < historyLebesgue 1 V) ∧
      ¬ (0 < ∫ t, ψ false t ∂historyLebesgue 1) := by
  refine ⟨fun b => if b then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro j x
    cases j <;> norm_num
  · intro x
    simp
  · exact historyLebesgue_full_support 1 (by norm_num)
  · simp

end

end GlobalRegularization
