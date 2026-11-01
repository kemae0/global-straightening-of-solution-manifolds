import GlobalRegularization.SignedMeasureDuality
import GlobalRegularization.TerminalCutoffAdjoint
import GlobalRegularization.ComposedAdjointApproximation

/-! The actual signed-measure adjoints and convergence in total variation,
including the Markov and terminal-cutoff operators of the manuscript. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped Topology NNReal

noncomputable section

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

def signedMeasureAdjoint (T : C(X, ℝ) →L[ℝ] C(X, ℝ)) (s : SignedMeasure X) : SignedMeasure X :=
  signedRieszMeasure ((signedIntegralFunctional s).comp T)

@[simp]
theorem signedMeasureAdjoint_represents (T : C(X, ℝ) →L[ℝ] C(X, ℝ)) (s : SignedMeasure X) :
    signedIntegralFunctional (signedMeasureAdjoint T s) = (signedIntegralFunctional s).comp T :=
  signedRieszMeasure_represents _

theorem signedMeasureAdjoint_variation_le (T : C(X, ℝ) →L[ℝ] C(X, ℝ)) (s : SignedMeasure X) :
    signedVariationNorm (signedMeasureAdjoint T s) ≤ ‖T‖ * signedVariationNorm s := by
  rw [signedVariationNorm_eq_dual_norm, signedMeasureAdjoint_represents,
    signedVariationNorm_eq_dual_norm, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem signedMeasureAdjoint_variation_defect (T : C(X, ℝ) →L[ℝ] C(X, ℝ)) (s : SignedMeasure X) :
    signedVariationNorm (signedMeasureAdjoint T s - s) =
      ‖(signedIntegralFunctional s).comp (T - ContinuousLinearMap.id ℝ C(X, ℝ))‖ := by
  rw [signedVariationNorm_eq_dual_norm, signedIntegralFunctional_sub, signedMeasureAdjoint_represents,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]

theorem signedMeasureAdjoint_variation_tendsto
    (T : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)) (s : SignedMeasure X)
    (hT : Tendsto (fun n => (signedIntegralFunctional s).comp
      (T n - ContinuousLinearMap.id ℝ C(X, ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n => signedVariationNorm (signedMeasureAdjoint (T n) s - s)) atTop (𝓝 0) := by
  simp only [signedMeasureAdjoint_variation_defect]
  exact (tendsto_zero_iff_norm_tendsto_zero (f := fun n => (signedIntegralFunctional s).comp
    (T n - ContinuousLinearMap.id ℝ C(X, ℝ)))).mp hT

theorem markovApproximation_signed_totalVariation
    (ν : Measure X) [IsFiniteMeasure ν]
    (hfull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < ν U)
    (s : SignedMeasure X) (hac : s.totalVariation ≪ ν) :
    Tendsto (fun n => signedVariationNorm (signedMeasureAdjoint (markovApproximation ℝ X ν n) s - s))
      atTop (𝓝 0) := by
  have hparts := (SignedMeasure.totalVariation_absolutelyContinuous_iff s ν).mp hac
  have hp := markovApproximation_measure_adjoint X ν hfull s.toJordanDecomposition.posPart hparts.1
  have hn := markovApproximation_measure_adjoint X ν hfull s.toJordanDecomposition.negPart hparts.2
  apply signedMeasureAdjoint_variation_tendsto
  simpa only [signedIntegralFunctional, ContinuousLinearMap.sub_comp, sub_self] using hp.sub hn

theorem terminalHistoryCutoff_signed_totalVariation
    (h : ℝ≥0) (s : SignedMeasure (HistoryInterval h)) (hs : s {historyRight h} = 0)
    (σ : ℕ → ℝ) (hσh : ∀ n, σ n ≤ (h : ℝ)) (hlim : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n => signedVariationNorm
      (signedMeasureAdjoint (terminalHistoryCutoff h ℝ (σ n) (hσh n)) s - s)) atTop (𝓝 0) := by
  have hatom := (signed_totalVariation_singleton_zero_iff s (historyRight h)).mpr hs
  have hparts : s.toJordanDecomposition.posPart {historyRight h} = 0 ∧
      s.toJordanDecomposition.negPart {historyRight h} = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hatom
  have hp := terminalHistoryCutoff_measure_adjoint h s.toJordanDecomposition.posPart hparts.1 σ hσh hlim
  have hn := terminalHistoryCutoff_measure_adjoint h s.toJordanDecomposition.negPart hparts.2 σ hσh hlim
  apply signedMeasureAdjoint_variation_tendsto
  simpa only [signedIntegralFunctional, ContinuousLinearMap.sub_comp, sub_self] using hp.sub hn

def finiteMarkovDensity {ι : Type*} [Fintype ι]
    (ν : Measure X) (ψ : ι → C(X, ℝ)) (w : X → ℝ) : C(X, ℝ) :=
  ∑ j, ((∫ t, ψ j t ∂ν)⁻¹ * ∫ t, ψ j t * w t ∂ν) • ψ j

theorem finiteMarkov_adjoint_density {ι : Type*} [Fintype ι]
    (ν : Measure X) [IsFiniteMeasure ν] (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1)
    (w : X → ℝ) (hw : Integrable w ν) :
    signedMeasureAdjoint (finiteMarkovOperator ℝ ν ψ hψ hsum)
      (signedRieszMeasure (integralDensityFunctional ν w hw)) =
    signedRieszMeasure (integralDensityFunctional ν (finiteMarkovDensity ν ψ w)
      (continuous_compact_integrable ν ℝ (finiteMarkovDensity ν ψ w))) := by
  apply signedIntegralFunctional_injective
  rw [signedMeasureAdjoint_represents, signedRieszMeasure_represents, signedRieszMeasure_represents]
  ext g
  change (∫ t, w t * finiteMarkovOperator ℝ ν ψ hψ hsum g t ∂ν) =
    ∫ t, finiteMarkovDensity ν ψ w t * g t ∂ν
  have hleft (t : X) : w t * finiteMarkovOperator ℝ ν ψ hψ hsum g t =
      ∑ j, (w t * ψ j t) * ((∫ s, ψ j s ∂ν)⁻¹ * ∫ s, ψ j s * g s ∂ν) := by
    rw [finiteMarkovOperator_apply]
    simp only [smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hright (t : X) : finiteMarkovDensity ν ψ w t * g t =
      ∑ j, ((∫ s, ψ j s ∂ν)⁻¹ * ∫ s, ψ j s * w s ∂ν) * (ψ j t * g t) := by
    simp only [finiteMarkovDensity, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, Finset.sum_mul, mul_assoc]
  simp_rw [hleft, hright]
  have hR : (∫ t, ∑ j, ((∫ s, ψ j s ∂ν)⁻¹ * ∫ s, ψ j s * w s ∂ν) * (ψ j t * g t) ∂ν) =
      ∑ j, ∫ t, ((∫ s, ψ j s ∂ν)⁻¹ * ∫ s, ψ j s * w s ∂ν) * (ψ j t * g t) ∂ν := by
    apply integral_finset_sum
    intro j _
    simpa only [ContinuousMap.mul_apply] using
      (continuous_compact_integrable ν ℝ (ψ j * g)).const_mul
        ((∫ s, ψ j s ∂ν)⁻¹ * ∫ s, ψ j s * w s ∂ν)
  rw [integral_finset_sum Finset.univ (fun j _ =>
      (integrable_density_mul_continuous ν hw (ψ j)).mul_const _), hR]
  simp only [integral_mul_const, integral_const_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hcomm : (∫ t, w t * ψ j t ∂ν) = ∫ t, ψ j t * w t ∂ν := by
    apply integral_congr_ae
    exact ae_of_all ν (fun t => mul_comm _ _)
  rw [hcomm]
  ring

theorem integral_terminalTailBound_eq (h : ℝ≥0)
    (μ : Measure (HistoryInterval h)) [IsFiniteMeasure μ] (σ : ℝ) :
    (∫ t, terminalTailBound h σ t ∂μ) = 2 * μ.real {t : HistoryInterval h | -σ < (t : ℝ)} := by
  have hm : MeasurableSet {t : HistoryInterval h | -σ < (t : ℝ)} :=
    measurableSet_lt measurable_const continuous_subtype_val.measurable
  have heq : terminalTailBound h σ =
      {t : HistoryInterval h | -σ < (t : ℝ)}.indicator (fun _ => (2 : ℝ)) := rfl
  rw [heq, integral_indicator_const _ hm]
  simp only [smul_eq_mul, mul_comm]

theorem terminalHistoryCutoff_signed_variation_bound
    (h : ℝ≥0) (s : SignedMeasure (HistoryInterval h)) (σ : ℝ) (hσh : σ ≤ (h : ℝ)) :
    signedVariationNorm (signedMeasureAdjoint (terminalHistoryCutoff h ℝ σ hσh) s - s) ≤
      2 * s.totalVariation.real {t : HistoryInterval h | -σ < (t : ℝ)} := by
  rw [signedMeasureAdjoint_variation_defect, signedIntegralFunctional, ContinuousLinearMap.sub_comp]
  have hp := norm_terminalHistoryCutoff_integral_defect_le h s.toJordanDecomposition.posPart σ hσh
  have hn := norm_terminalHistoryCutoff_integral_defect_le h s.toJordanDecomposition.negPart σ hσh
  rw [integral_terminalTailBound_eq] at hp hn
  refine (norm_sub_le _ _).trans ((add_le_add hp hn).trans_eq ?_)
  rw [SignedMeasure.totalVariation, measureReal_add_apply]
  ring

theorem composed_signed_adjoint_totalVariation
    (T V : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)) (hV : ∀ n, ‖V n‖ ≤ 1) (s : SignedMeasure X)
    (hTlim : Tendsto (fun n => signedVariationNorm (signedMeasureAdjoint (T n) s - s)) atTop (𝓝 0))
    (hVlim : Tendsto (fun n => signedVariationNorm (signedMeasureAdjoint (V n) s - s)) atTop (𝓝 0)) :
    Tendsto (fun n => signedVariationNorm (signedMeasureAdjoint ((T n).comp (V n)) s - s)) atTop (𝓝 0) := by
  apply signedMeasureAdjoint_variation_tendsto
  apply composed_adjoint_contractions_tendsto T V hV (signedIntegralFunctional s)
  · apply (tendsto_zero_iff_norm_tendsto_zero (f := fun n =>
      (signedIntegralFunctional s).comp (T n - ContinuousLinearMap.id ℝ C(X, ℝ)))).mpr
    simpa only [signedMeasureAdjoint_variation_defect] using hTlim
  · apply (tendsto_zero_iff_norm_tendsto_zero (f := fun n =>
      (signedIntegralFunctional s).comp (V n - ContinuousLinearMap.id ℝ C(X, ℝ)))).mpr
    simpa only [signedMeasureAdjoint_variation_defect] using hVlim

end

end GlobalRegularization
