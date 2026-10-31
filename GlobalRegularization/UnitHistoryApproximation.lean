import GlobalRegularization.HistorySpace
import GlobalRegularization.BernsteinCoefficientConvergence

/-! Actual Bernstein approximations in the complete `C¹([-1,0], B)`
history space, with strong convergence in the `C¹` norm. -/

namespace GlobalRegularization

open Filter
open scoped unitInterval NNReal Topology

noncomputable section

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def unitHistoryShift : C(HistoryInterval 1, I) :=
  ⟨fun t => ⟨(t : ℝ) + 1, by
      have hl := t.property.1
      have hr := t.property.2
      change -(1 : ℝ) ≤ (t : ℝ) at hl
      constructor <;> linarith⟩,
    by fun_prop⟩

def unitHistoryGlobalValue (x : C1History 1 B) (t : ℝ) : B :=
  differentiableHistoryExtension 1 B x (t - 1)

def unitHistoryGlobalDerivative (x : C1History 1 B) (t : ℝ) : B :=
  extendHistory 1 B (historyDerivative 1 B x) (t - 1)

theorem unitHistoryGlobal_hasDerivAt (x : C1History 1 B) (t : ℝ) :
    HasDerivAt (unitHistoryGlobalValue B x) (unitHistoryGlobalDerivative B x t) t := by
  simpa only [unitHistoryGlobalValue, unitHistoryGlobalDerivative, Function.comp_def, one_smul] using
    (hasDerivAt_historyExtension_all 1 B x (t - 1)).scomp t ((hasDerivAt_id t).sub_const 1)

theorem unitHistoryGlobalDerivative_uniformContinuous (x : C1History 1 B) :
    UniformContinuous (unitHistoryGlobalDerivative B x) :=
  (uniformContinuous_extendHistory 1 B (historyDerivative 1 B x)).comp
    ((LipschitzWith.id.sub (LipschitzWith.const (1 : ℝ))).uniformContinuous)

theorem unitHistoryGlobalDerivative_bound (x : C1History 1 B) (t : ℝ) :
    ‖unitHistoryGlobalDerivative B x t‖ ≤ ‖historyDerivative 1 B x‖ :=
  (historyDerivative 1 B x).norm_coe_le_norm _

theorem unitHistoryGlobalValue_bound (x : C1History 1 B) (s : I) :
    ‖unitHistoryGlobalValue B x s‖ ≤ ‖historyInclusion 1 B x‖ := by
  let t : HistoryInterval 1 := ⟨(s : ℝ) - 1, by
    change -(1 : ℝ) ≤ (s : ℝ) - 1 ∧ (s : ℝ) - 1 ≤ 0
    constructor <;> linarith [s.property.1, s.property.2]⟩
  have heq : unitHistoryGlobalValue B x s = historyInclusion 1 B x t :=
    differentiableHistoryExtension_coe 1 B x t
  rw [heq]
  exact (historyInclusion 1 B x).norm_coe_le_norm t

def unitHistoryBernstein (n : ℕ) (x : C1History 1 B) : C1History 1 B :=
  historyOfC1Function 1 B
    (fun t => bernsteinCurve (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B x) n) (t + 1))
    (fun t => bernsteinCurve n
      (bernsteinDifferenceCoefficients n (bernsteinCurveSamples (unitHistoryGlobalValue B x) n)) (t + 1))
    ((continuous_bernsteinCurve _ _).comp (continuous_id.add continuous_const))
    ((continuous_bernsteinCurve _ _).comp (continuous_id.add continuous_const))
    (fun t => by
      simpa only [Function.comp_def, one_smul] using
        (hasDerivAt_bernsteinCurve_difference n
          (bernsteinCurveSamples (unitHistoryGlobalValue B x) n) (t + 1)).scomp t
            ((hasDerivAt_id t).add_const 1))

theorem norm_unitHistoryBernstein_value_le (n : ℕ) (x : C1History 1 B) :
    ‖historyInclusion 1 B (unitHistoryBernstein B n x)‖ ≤ ‖historyInclusion 1 B x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  apply norm_bernsteinCurve_le (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B x) n)
    (norm_nonneg _) _ (unitHistoryShift t)
  intro k hk
  let s : I := ⟨(k : ℝ) / (n + 1 : ℝ), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (n + 1 : ℝ))).2
      exact_mod_cast hk⟩
  exact unitHistoryGlobalValue_bound B x s

theorem norm_unitHistoryBernstein_derivative_le (n : ℕ) (x : C1History 1 B) :
    ‖historyDerivative 1 B (unitHistoryBernstein B n x)‖ ≤ ‖historyDerivative 1 B x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  apply norm_bernsteinCurve_le n
    (bernsteinDifferenceCoefficients n (bernsteinCurveSamples (unitHistoryGlobalValue B x) n))
    (norm_nonneg _) _ (unitHistoryShift t)
  intro k hk
  exact norm_bernsteinDifferenceCoefficients_le _ _ (unitHistoryGlobal_hasDerivAt B x)
    (unitHistoryGlobalDerivative_bound B x) n k

theorem norm_unitHistoryBernstein_le (n : ℕ) (x : C1History 1 B) :
    ‖unitHistoryBernstein B n x‖ ≤ ‖x‖ :=
  max_le_max (norm_unitHistoryBernstein_value_le B n x)
    (norm_unitHistoryBernstein_derivative_le B n x)

def unitHistoryBernsteinL (n : ℕ) : C1History 1 B →ₗ[ℝ] C1History 1 B where
  toFun := unitHistoryBernstein B n
  map_add' x y := by
    apply historyInclusion_injective 1 B (by norm_num)
    ext t
    change bernsteinCurve (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B (x + y)) n) ((t : ℝ) + 1) =
      bernsteinCurve (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B x) n) ((t : ℝ) + 1) +
      bernsteinCurve (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B y) n) ((t : ℝ) + 1)
    simp [bernsteinCurve, bernsteinCurveSamples, unitHistoryGlobalValue,
      differentiableHistoryExtension_add, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    apply historyInclusion_injective 1 B (by norm_num)
    ext t
    change bernsteinCurve (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B (c • x)) n) ((t : ℝ) + 1) =
      c • bernsteinCurve (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B x) n) ((t : ℝ) + 1)
    change bernsteinCurve (n + 1)
      (fun k => differentiableHistoryExtension 1 B (c • x) ((k : ℝ) / (n + 1 : ℝ) - 1)) ((t : ℝ) + 1) =
      c • bernsteinCurve (n + 1)
        (fun k => differentiableHistoryExtension 1 B x ((k : ℝ) / (n + 1 : ℝ) - 1)) ((t : ℝ) + 1)
    simp_rw [differentiableHistoryExtension_smul]
    exact bernsteinCurve_coeff_smul (n + 1) _ c ((t : ℝ) + 1)

def unitHistoryBernsteinCLM (n : ℕ) : C1History 1 B →L[ℝ] C1History 1 B :=
  (unitHistoryBernsteinL B n).mkContinuous 1
    (fun x => by simpa only [one_mul] using norm_unitHistoryBernstein_le B n x)

theorem norm_unitHistoryBernsteinCLM_le (n : ℕ) : ‖unitHistoryBernsteinCLM B n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simpa only [one_mul] using norm_unitHistoryBernstein_le B n x)

omit [CompleteSpace B] in
theorem bernsteinCurveSamples_eq_approximation (u : ℝ → B) (hu : Continuous u) (n : ℕ) :
    bernsteinCurveCM (n + 1) (bernsteinCurveSamples u n) =
      bernsteinApproximation (n + 1) (restrictToUnitInterval u hu) := by
  rw [bernsteinCurveCM_eq_synthesis, ← bernsteinCLM_eq]
  change bernsteinSynthesis B (n + 1) _ = bernsteinSynthesis B (n + 1) _
  congr 1
  ext k
  simp [bernsteinCurveSamples, bernsteinSamples_apply, restrictToUnitInterval,
    bernstein.z, Nat.cast_add, Nat.cast_one]

theorem unitHistoryBernstein_strong (x : C1History 1 B) :
    Tendsto (fun n => unitHistoryBernstein B n x) atTop (𝓝 x) := by
  let u := unitHistoryGlobalValue B x
  let g := unitHistoryGlobalDerivative B x
  have hu : ∀ t, HasDerivAt u (g t) t := unitHistoryGlobal_hasDerivAt B x
  have huc : Continuous u := continuous_iff_continuousAt.mpr (fun t => (hu t).continuousAt)
  have hgu : UniformContinuous g := unitHistoryGlobalDerivative_uniformContinuous B x
  have hv : Tendsto (fun n => bernsteinCurveCM (n + 1) (bernsteinCurveSamples u n))
      atTop (𝓝 (restrictToUnitInterval u huc)) := by
    simpa only [bernsteinCurveSamples_eq_approximation B u huc] using
      (bernsteinApproximation_uniform (restrictToUnitInterval u huc)).comp (tendsto_add_atTop_nat 1)
  have hd := bernstein_derivatives_converge u g hu hgu
  have hpv := (ContinuousMap.continuous_precomp (unitHistoryShift)).tendsto
    (restrictToUnitInterval u huc)
  have hpd := (ContinuousMap.continuous_precomp (unitHistoryShift)).tendsto
    (restrictToUnitInterval g hgu.continuous)
  have hvlim : (restrictToUnitInterval u huc).comp unitHistoryShift = historyInclusion 1 B x := by
    ext t
    change differentiableHistoryExtension 1 B x ((t : ℝ) + 1 - 1) = _
    rw [add_sub_cancel_right]
    exact differentiableHistoryExtension_coe 1 B x t
  have hdlim : (restrictToUnitInterval g hgu.continuous).comp unitHistoryShift = historyDerivative 1 B x := by
    ext t
    change extendHistory 1 B (historyDerivative 1 B x) ((t : ℝ) + 1 - 1) = _
    rw [add_sub_cancel_right, extendHistory_coe]
  have hvalues : Tendsto (fun n => historyInclusion 1 B (unitHistoryBernstein B n x))
      atTop (𝓝 (historyInclusion 1 B x)) := by
    simpa only [hvlim] using hpv.comp hv
  have hderivatives : Tendsto (fun n => historyDerivative 1 B (unitHistoryBernstein B n x))
      atTop (𝓝 (historyDerivative 1 B x)) := by
    simpa only [hdlim] using hpd.comp hd
  apply tendsto_subtype_rng.mpr
  exact hvalues.prodMk_nhds hderivatives

end

end GlobalRegularization
