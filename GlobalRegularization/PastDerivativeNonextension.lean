import GlobalRegularization.PastDerivativeApplication

/-! The past-derivative example really lies beyond property (e): at the
zero history its derivative has no continuous-history extension. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

def shiftedTerminalScalarHistory (h : ℝ≥0) (t : HistoryInterval h) (δ : ℝ) (hδ : 0 < δ) : C1History h ℝ :=
  historyOfC1Function h ℝ (fun s => terminalProfile δ hδ (s - t))
    (fun s => deriv (terminalProfile δ hδ) (s - t))
    ((terminalProfile_contDiff δ hδ).continuous.comp (continuous_id.sub continuous_const))
    ((terminalProfile_contDiff δ hδ).continuous_deriv_one.comp (continuous_id.sub continuous_const))
    (fun s => by
      simpa only [Function.comp_def, one_smul] using
        (((terminalProfile_contDiff δ hδ).differentiable_one (s - t)).hasDerivAt).scomp s
          ((hasDerivAt_id s).sub_const (t : ℝ)))

theorem shiftedTerminalScalarHistory_small (h : ℝ≥0) (t : HistoryInterval h) (δ : ℝ) (hδ : 0 < δ) :
    ‖historyInclusion h ℝ (shiftedTerminalScalarHistory h t δ hδ)‖ ≤ δ / 2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro s
  exact abs_terminalProfile_le δ hδ ((s : ℝ) - t)

theorem pastDerivative_has_no_continuous_extension (h : ℝ≥0) (t : HistoryInterval h) :
    ¬ ∃ L : ContinuousHistory h ℝ →L[ℝ] ℝ,
      historyDerivativeAt h ℝ t = L.comp (historyInclusion h ℝ) := by
  rintro ⟨L, hL⟩
  let δ : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hδ (n : ℕ) : 0 < δ n := by positivity
  let x := fun n => shiftedTerminalScalarHistory h t (δ n) (hδ n)
  have hx : Tendsto (fun n => historyInclusion h ℝ (x n)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero (f := fun n => historyInclusion h ℝ (x n))).mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => shiftedTerminalScalarHistory_small h t (δ n) (hδ n))
    simpa only [zero_div] using tendsto_one_div_add_atTop_nhds_zero_nat.div_const 2
  have ht := (L.continuous.tendsto 0).comp hx
  have he (n : ℕ) : L (historyInclusion h ℝ (x n)) = 1 := by
    have hn := congrArg (fun F : C1History h ℝ →L[ℝ] ℝ => F (x n)) hL
    change deriv (terminalProfile (δ n) (hδ n)) ((t : ℝ) - t) = L (historyInclusion h ℝ (x n)) at hn
    rw [sub_self, terminalProfile_deriv_zero] at hn
    exact hn.symm
  simp only [Function.comp_def, he, map_zero] at ht
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at h10

def scalarPastDerivativeFeedback (h : ℝ≥0) (t s : HistoryInterval h) (x : C1History h ℝ) : ℝ :=
  Real.sin (historyDerivative h ℝ x t) + (historyInclusion h ℝ x s) ^ 3

theorem scalarPastDerivativeFeedback_derivative_zero (h : ℝ≥0) (t s : HistoryInterval h) :
    fderiv ℝ (scalarPastDerivativeFeedback h t s) 0 = historyDerivativeAt h ℝ t := by
  let D := historyDerivativeAt h ℝ t
  let V := (ContinuousMap.evalCLM ℝ s).comp (historyInclusion h ℝ)
  have hd : HasFDerivAt D D (0 : C1History h ℝ) := D.hasFDerivAt
  have hv : HasFDerivAt V V (0 : C1History h ℝ) := V.hasFDerivAt
  have h := hd.sin.add (hv.pow 3)
  simpa [scalarPastDerivativeFeedback, D, V] using h.fderiv

theorem scalarPastDerivativeFeedback_no_extended_derivative_at_zero
    (h : ℝ≥0) (t s : HistoryInterval h) :
    ¬ ∃ L : ContinuousHistory h ℝ →L[ℝ] ℝ,
      fderiv ℝ (scalarPastDerivativeFeedback h t s) 0 = L.comp (historyInclusion h ℝ) := by
  rw [scalarPastDerivativeFeedback_derivative_zero]
  exact pastDerivative_has_no_continuous_extension h t

end

end GlobalRegularization
