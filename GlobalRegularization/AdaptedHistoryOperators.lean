import GlobalRegularization.ReconstructedApproximants
import GlobalRegularization.TerminalCutoffAdjoint
import GlobalRegularization.ComposedAdjointApproximation

/-! Actual adapted history operators from the constructed Markov
averages and shrinking terminal cutoffs. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section

instance (h : ℝ≥0) : MetricSpace (HistoryInterval h) :=
  inferInstanceAs (MetricSpace (Set.Icc (-(h : ℝ)) 0))

def adaptedTerminalWidth (h : ℝ≥0) (n : ℕ) : ℝ := (h : ℝ) / (n + 2 : ℝ)

theorem adaptedTerminalWidth_le (h : ℝ≥0) (n : ℕ) : adaptedTerminalWidth h n ≤ (h : ℝ) := by
  apply (div_le_iff₀ (show (0 : ℝ) < n + 2 by positivity)).mpr
  nlinarith [h.coe_nonneg, Nat.cast_nonneg (α := ℝ) n]

theorem adaptedTerminalWidth_pos (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ) :
    0 < adaptedTerminalWidth h n := div_pos hh (by positivity)

theorem adaptedTerminalWidth_tendsto (h : ℝ≥0) : Tendsto (adaptedTerminalWidth h) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => 1 / (n + 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [adaptedTerminalWidth, mul_one_div, mul_zero] using ht.const_mul (h : ℝ)

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  (ν : Measure (HistoryInterval h)) [IsFiniteMeasure ν]

def adaptedDerivativeOperator (n : ℕ) : ContinuousHistory h B →L[ℝ] ContinuousHistory h B :=
  (markovApproximation B (HistoryInterval h) ν n).comp
    (terminalHistoryCutoff h B (adaptedTerminalWidth h n) (adaptedTerminalWidth_le h n))

def adaptedHistoryOperator (n : ℕ) : C1History h B →L[ℝ] C1History h B :=
  reconstructHistoryOperator h B (adaptedDerivativeOperator h B ν n)

theorem norm_adaptedDerivativeOperator_le (n : ℕ) : ‖adaptedDerivativeOperator h B ν n‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hT := norm_markovApproximation_le B (HistoryInterval h) ν n
  have hV := norm_terminalHistoryCutoff_le h B (adaptedTerminalWidth h n) (adaptedTerminalWidth_le h n)
  exact (mul_le_mul hT hV (norm_nonneg _) zero_le_one).trans (by norm_num)

theorem adaptedHistoryOperator_uniform_bound (n : ℕ) :
    ‖adaptedHistoryOperator h B ν n‖ ≤ ‖(historyCoordinates h B).symm.toContinuousLinearMap‖ :=
  norm_reconstructHistoryOperator_le h B _ (norm_adaptedDerivativeOperator_le h B ν n)

theorem adaptedDerivativeOperator_strong
    (hfull : ∀ U : Set (HistoryInterval h), IsOpen U → U.Nonempty → 0 < ν U)
    (g : ContinuousHistory h B) : Tendsto (fun n => adaptedDerivativeOperator h B ν n g) atTop (𝓝 g) := by
  apply composed_contractions_strong h B (markovApproximation B (HistoryInterval h) ν)
    (fun n => terminalHistoryCutoff h B (adaptedTerminalWidth h n) (adaptedTerminalWidth_le h n))
    (norm_markovApproximation_le B (HistoryInterval h) ν) (markovApproximation_strong B (HistoryInterval h) ν hfull)
  intro f
  exact terminalHistoryCutoff_strong h B (adaptedTerminalWidth h)
    (fun n => by unfold adaptedTerminalWidth; positivity) (adaptedTerminalWidth_le h)
    (adaptedTerminalWidth_tendsto h) f

theorem adaptedHistoryOperator_strong
    (hfull : ∀ U : Set (HistoryInterval h), IsOpen U → U.Nonempty → 0 < ν U)
    (x : C1History h B) : Tendsto (fun n => adaptedHistoryOperator h B ν n x) atTop (𝓝 x) :=
  reconstructHistoryOperator_strong h B _ (adaptedDerivativeOperator_strong h B ν hfull) x

theorem adaptedHistoryOperator_finite_range [FiniteDimensional ℝ B] (n : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (adaptedHistoryOperator h B ν n)) := by
  let T := markovApproximation B (HistoryInterval h) ν n
  have hr : LinearMap.range (adaptedDerivativeOperator h B ν n) ≤ LinearMap.range T := by
    rintro y ⟨g, rfl⟩
    exact ⟨terminalHistoryCutoff h B (adaptedTerminalWidth h n) (adaptedTerminalWidth_le h n) g, rfl⟩
  letI := markovApproximation_finite_range B (HistoryInterval h) ν n
  letI : FiniteDimensional ℝ (LinearMap.range (adaptedDerivativeOperator h B ν n)) :=
    FiniteDimensional.of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
  exact reconstructHistoryOperator_finite_range h B _

theorem adaptedHistoryOperator_annihilates_terminal (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hshort : δ / 2 < adaptedTerminalWidth h n) :
    (adaptedHistoryOperator h B ν n).comp (terminalCorrection h B δ hδ) = 0 :=
  reconstructHistoryOperator_annihilates_terminal h B _ (adaptedTerminalWidth h n)
    (adaptedTerminalWidth_le h n) δ hδ hshort

theorem adaptedDerivativeOperator_measure_adjoint [ν.WeaklyRegular]
    (hfull : ∀ U : Set (HistoryInterval h), IsOpen U → U.Nonempty → 0 < ν U)
    (μ : Measure (HistoryInterval h)) [IsFiniteMeasure μ] (hac : μ ≪ ν) (hatom : μ {historyRight h} = 0) :
    Tendsto (fun n => (continuousIntegralFunctional (HistoryInterval h) μ).comp
      (adaptedDerivativeOperator h ℝ ν n - ContinuousLinearMap.id ℝ (ContinuousHistory h ℝ))) atTop (𝓝 0) := by
  apply composed_adjoint_contractions_tendsto
    (markovApproximation ℝ (HistoryInterval h) ν)
    (fun n => terminalHistoryCutoff h ℝ (adaptedTerminalWidth h n) (adaptedTerminalWidth_le h n))
    (fun n => norm_terminalHistoryCutoff_le h ℝ _ _) (continuousIntegralFunctional (HistoryInterval h) μ)
  · exact markovApproximation_measure_adjoint (HistoryInterval h) ν hfull μ hac
  · exact terminalHistoryCutoff_measure_adjoint h μ hatom _ (adaptedTerminalWidth_le h) (adaptedTerminalWidth_tendsto h)

end

end GlobalRegularization
