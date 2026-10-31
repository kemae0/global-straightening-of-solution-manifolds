import GlobalRegularization.HistoryFunctionalRepresentation
import GlobalRegularization.TerminalAtomLimit

/-! The endpoint-atom calculation on the actual compact history
interval, and the scalar history-functional terminal limit. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section

theorem integral_history_terminalProfile_deriv_tendsto_atom
    (h : ℝ≥0) (μ : Measure (HistoryInterval h)) [IsFiniteMeasure μ]
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t : HistoryInterval h, deriv (terminalProfile (δ n) (hδ n)) t ∂μ)
      atTop (𝓝 (μ.real {historyRight h})) := by
  obtain ⟨M, hM⟩ := exists_terminalProfile_derivative_bound
  have hind (t : HistoryInterval h) :
      ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) (t : ℝ) =
        ({historyRight h} : Set (HistoryInterval h)).indicator (fun _ => (1 : ℝ)) t := by
    by_cases ht : t = historyRight h
    · subst t
      simp [historyRight]
    · have ht₀ : (t : ℝ) ≠ 0 := fun hz => ht (Subtype.ext hz)
      simp [ht, ht₀]
  have hp (t : HistoryInterval h) := terminalProfile_deriv_tendsto_indicator δ hδ hlim (t : ℝ)
  simp only [hind] at hp
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ : HistoryInterval h => M)
    (fun n => ((terminalProfile_contDiff (δ n) (hδ n)).continuous_deriv_one.comp
      continuous_subtype_val).aestronglyMeasurable)
    (integrable_const M)
    (fun n => ae_of_all μ (fun t => hM (δ n) (hδ n) t)) (ae_of_all μ hp)
  simpa only [integral_indicator_const (1 : ℝ) (measurableSet_singleton (historyRight h)),
    smul_eq_mul, mul_one] using ht

theorem scalarHistoryFunctional_terminal_limit_of_representation
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (L : C1History h ℝ →L[ℝ] ℝ)
    (b : ℝ) (μ ν : Measure (HistoryInterval h)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hrep : ∀ x, L x = b * historyInclusion h ℝ x (historyLeft h) +
      (∫ t, historyDerivative h ℝ x t ∂μ) - ∫ t, historyDerivative h ℝ x t ∂ν)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => L (terminalCorrection h ℝ (δ n) (hδ n) 1)) atTop
      (𝓝 (μ.real {historyRight h} - ν.real {historyRight h})) := by
  have hleft : Tendsto (fun n => historyInclusion h ℝ (terminalCorrection h ℝ (δ n) (hδ n) 1)
      (historyLeft h)) atTop (𝓝 0) := by
    have hevent : ∀ᶠ n : ℕ in atTop, δ n < 2 * (h : ℝ) :=
      hlim.eventually (Iio_mem_nhds (by positivity))
    have hz : (fun n => historyInclusion h ℝ (terminalCorrection h ℝ (δ n) (hδ n) 1)
        (historyLeft h)) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [hevent] with n hn
      apply terminalCorrection_localized h ℝ (δ n) (hδ n) 1 (historyLeft h)
      change -(h : ℝ) ≤ -δ n / 2
      linarith
    exact (tendsto_congr' hz).mpr tendsto_const_nhds
  have hder (n : ℕ) (t : HistoryInterval h) :
      historyDerivative h ℝ (terminalCorrection h ℝ (δ n) (hδ n) 1) t =
        deriv (terminalProfile (δ n) (hδ n)) t := by
    change deriv (terminalProfile (δ n) (hδ n)) t • (1 : ℝ) = _
    simp only [smul_eq_mul, mul_one]
  have heq (n : ℕ) : L (terminalCorrection h ℝ (δ n) (hδ n) 1) =
      b * historyInclusion h ℝ (terminalCorrection h ℝ (δ n) (hδ n) 1) (historyLeft h) +
        (∫ t : HistoryInterval h, deriv (terminalProfile (δ n) (hδ n)) t ∂μ) -
        ∫ t : HistoryInterval h, deriv (terminalProfile (δ n) (hδ n)) t ∂ν := by
    simpa only [hder] using hrep (terminalCorrection h ℝ (δ n) (hδ n) 1)
  have ht := ((hleft.const_mul b).add (integral_history_terminalProfile_deriv_tendsto_atom h μ δ hδ hlim)).sub
    (integral_history_terminalProfile_deriv_tendsto_atom h ν δ hδ hlim)
  simpa only [heq, mul_zero, zero_add] using ht

theorem scalarCLM_eq_value_smul_id (T : ℝ →L[ℝ] ℝ) :
    T = T 1 • ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro a
  have hm := T.map_smul a (1 : ℝ)
  simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one, mul_comm] using hm

theorem scalarHistoryFunctional_terminal_operator_limit
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (L : C1History h ℝ →L[ℝ] ℝ)
    (b : ℝ) (μ ν : Measure (HistoryInterval h)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hrep : ∀ x, L x = b * historyInclusion h ℝ x (historyLeft h) +
      (∫ t, historyDerivative h ℝ x t ∂μ) - ∫ t, historyDerivative h ℝ x t ∂ν)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => L.comp (terminalCorrection h ℝ (δ n) (hδ n))) atTop
      (𝓝 ((μ.real {historyRight h} - ν.real {historyRight h}) • ContinuousLinearMap.id ℝ ℝ)) := by
  have ht := (scalarHistoryFunctional_terminal_limit_of_representation h hh L b μ ν hrep δ hδ hlim).smul_const
    (ContinuousLinearMap.id ℝ ℝ)
  have heq (n : ℕ) : L.comp (terminalCorrection h ℝ (δ n) (hδ n)) =
      L (terminalCorrection h ℝ (δ n) (hδ n) 1) • ContinuousLinearMap.id ℝ ℝ :=
    scalarCLM_eq_value_smul_id _
  change Tendsto (fun n => L.comp (terminalCorrection h ℝ (δ n) (hδ n))) atTop _
  simpa only [heq] using ht

theorem scalarHistoryFunctional_terminal_zero_iff
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (L : C1History h ℝ →L[ℝ] ℝ)
    (b : ℝ) (μ ν : Measure (HistoryInterval h)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hrep : ∀ x, L x = b * historyInclusion h ℝ x (historyLeft h) +
      (∫ t, historyDerivative h ℝ x t ∂μ) - ∫ t, historyDerivative h ℝ x t ∂ν)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => L.comp (terminalCorrection h ℝ (δ n) (hδ n))) atTop (𝓝 0) ↔
      μ.real {historyRight h} - ν.real {historyRight h} = 0 := by
  have ht := scalarHistoryFunctional_terminal_operator_limit h hh L b μ ν hrep δ hδ hlim
  constructor
  · intro hzero
    have heq := tendsto_nhds_unique ht hzero
    have hval := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) heq
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, mul_one] using hval
  · intro hzero
    simpa only [hzero, zero_smul] using ht

end

end GlobalRegularization
