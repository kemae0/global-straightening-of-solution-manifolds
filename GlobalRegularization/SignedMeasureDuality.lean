import GlobalRegularization.MarkovAdjoint
import GlobalRegularization.ScalarRieszRepresentation
import GlobalRegularization.CommonDominatingMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Signed Riesz measures, uniqueness and the actual total-variation norm.
The norm below is the mass of mathlib's Jordan total-variation measure,
not a substitute defined by the continuous dual norm. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

def signedVariationNorm (s : SignedMeasure X) : ℝ := s.totalVariation.real univ

def signedIntegralFunctional (s : SignedMeasure X) : C(X, ℝ) →L[ℝ] ℝ :=
  continuousIntegralFunctional X s.toJordanDecomposition.posPart -
    continuousIntegralFunctional X s.toJordanDecomposition.negPart

@[simp]
theorem signedIntegralFunctional_apply (s : SignedMeasure X) (g : C(X, ℝ)) :
    signedIntegralFunctional s g = (∫ x, g x ∂s.toJordanDecomposition.posPart) -
      ∫ x, g x ∂s.toJordanDecomposition.negPart := by
  simp only [signedIntegralFunctional, ContinuousLinearMap.sub_apply, continuousIntegralFunctional_apply]

theorem measure_difference_unique
    (μ ν ρ σ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (heq : ∀ g : C(X, ℝ), (∫ x, g x ∂μ) - (∫ x, g x ∂ν) =
      (∫ x, g x ∂ρ) - (∫ x, g x ∂σ)) :
    μ.toSignedMeasure - ν.toSignedMeasure = ρ.toSignedMeasure - σ.toSignedMeasure := by
  have h : μ + σ = ρ + ν := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    have hg := heq g.toContinuousMap
    change (∫ x, g x ∂μ) - (∫ x, g x ∂ν) = (∫ x, g x ∂ρ) - (∫ x, g x ∂σ) at hg
    rw [integral_add_measure (g.integrable μ) (g.integrable σ),
      integral_add_measure (g.integrable ρ) (g.integrable ν)]
    linarith
  have hs := Measure.toSignedMeasure_congr h
  simp only [Measure.toSignedMeasure_add] at hs
  exact sub_eq_sub_iff_add_eq_add.mpr hs

theorem signedIntegralFunctional_of_difference
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    signedIntegralFunctional (μ.toSignedMeasure - ν.toSignedMeasure) =
      continuousIntegralFunctional X μ - continuousIntegralFunctional X ν := by
  let s := μ.toSignedMeasure - ν.toSignedMeasure
  let j := s.toJordanDecomposition
  have h : j.posPart + ν = μ + j.negPart := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    simp only [Measure.toSignedMeasure_add]
    have hs := SignedMeasure.toSignedMeasure_toJordanDecomposition s
    change j.posPart.toSignedMeasure - j.negPart.toSignedMeasure =
      μ.toSignedMeasure - ν.toSignedMeasure at hs
    exact sub_eq_sub_iff_add_eq_add.mp hs
  apply ContinuousLinearMap.ext
  intro g
  have hg := congrArg (fun m : Measure X => ∫ x, g x ∂m) h
  dsimp only at hg
  rw [integral_add_measure (continuous_compact_integrable _ ℝ g) (continuous_compact_integrable _ ℝ g),
    integral_add_measure (continuous_compact_integrable _ ℝ g) (continuous_compact_integrable _ ℝ g)] at hg
  simp only [signedIntegralFunctional_apply, ContinuousLinearMap.sub_apply,
    continuousIntegralFunctional_apply]
  change (∫ x, g x ∂j.posPart) - (∫ x, g x ∂j.negPart) = _
  linarith

theorem signedIntegralFunctional_injective :
    Function.Injective (signedIntegralFunctional (X := X)) := by
  intro s t hst
  have h := measure_difference_unique s.toJordanDecomposition.posPart s.toJordanDecomposition.negPart
    t.toJordanDecomposition.posPart t.toJordanDecomposition.negPart (fun g => by
      simpa only [signedIntegralFunctional_apply] using
        congrArg (fun F : C(X, ℝ) →L[ℝ] ℝ => F g) hst)
  change s.toJordanDecomposition.toSignedMeasure = t.toJordanDecomposition.toSignedMeasure at h
  simpa only [SignedMeasure.toSignedMeasure_toJordanDecomposition] using h

theorem signedIntegralFunctional_sub (s t : SignedMeasure X) :
    signedIntegralFunctional (s - t) = signedIntegralFunctional s - signedIntegralFunctional t := by
  let p := s.toJordanDecomposition.posPart + t.toJordanDecomposition.negPart
  let q := s.toJordanDecomposition.negPart + t.toJordanDecomposition.posPart
  have heq : s - t = p.toSignedMeasure - q.toSignedMeasure := by
    dsimp only [p, q]
    simp only [Measure.toSignedMeasure_add]
    have hs := SignedMeasure.toSignedMeasure_toJordanDecomposition s
    have ht := SignedMeasure.toSignedMeasure_toJordanDecomposition t
    simp only [JordanDecomposition.toSignedMeasure] at hs ht
    calc
      s - t = (s.toJordanDecomposition.posPart.toSignedMeasure - s.toJordanDecomposition.negPart.toSignedMeasure) -
        (t.toJordanDecomposition.posPart.toSignedMeasure - t.toJordanDecomposition.negPart.toSignedMeasure) :=
          congrArg₂ (· - ·) hs.symm ht.symm
      _ = _ := by abel
  rw [heq, signedIntegralFunctional_of_difference]
  apply ContinuousLinearMap.ext
  intro g
  simp only [ContinuousLinearMap.sub_apply, continuousIntegralFunctional_apply, signedIntegralFunctional_apply]
  change (∫ x, g x ∂p) - (∫ x, g x ∂q) = _
  dsimp only [p, q]
  rw [integral_add_measure (continuous_compact_integrable _ ℝ g) (continuous_compact_integrable _ ℝ g),
    integral_add_measure (continuous_compact_integrable _ ℝ g) (continuous_compact_integrable _ ℝ g)]
  change _ = ((∫ x, g x ∂s.toJordanDecomposition.posPart) -
    (∫ x, g x ∂s.toJordanDecomposition.negPart)) -
    ((∫ x, g x ∂t.toJordanDecomposition.posPart) -
      (∫ x, g x ∂t.toJordanDecomposition.negPart))
  ring

theorem signedVariationNorm_nonneg (s : SignedMeasure X) : 0 ≤ signedVariationNorm s :=
  ENNReal.toReal_nonneg

theorem signedVariationNorm_le_of_difference
    (s : SignedMeasure X) (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hs : s = μ.toSignedMeasure - ν.toSignedMeasure) :
    signedVariationNorm s ≤ μ.real univ + ν.real univ := by
  let j := s.toJordanDecomposition
  obtain ⟨u, hu, hp, hn⟩ := j.mutuallySingular
  have heq (v : Set X) (hv : MeasurableSet v) :
      j.posPart.real v - j.negPart.real v = μ.real v - ν.real v := by
    have h := congrArg (fun m : SignedMeasure X => m v)
      ((SignedMeasure.toSignedMeasure_toJordanDecomposition s).trans hs)
    simpa only [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hv] using h
  have hp0 : j.posPart.real u = 0 := by simp only [measureReal_def, hp, ENNReal.toReal_zero]
  have hn0 : j.negPart.real uᶜ = 0 := by simp only [measureReal_def, hn, ENNReal.toReal_zero]
  have h₁ := heq u hu
  have h₂ := heq uᶜ hu.compl
  have hpm := measureReal_add_measureReal_compl (μ := j.posPart) hu
  have hnm := measureReal_add_measureReal_compl (μ := j.negPart) hu
  have hμ := measureReal_mono (μ := μ) (subset_univ uᶜ)
  have hν := measureReal_mono (μ := ν) (subset_univ u)
  have hμ0 : 0 ≤ μ.real u := ENNReal.toReal_nonneg
  have hν0 : 0 ≤ ν.real uᶜ := ENNReal.toReal_nonneg
  change (j.posPart + j.negPart).real univ ≤ _
  rw [measureReal_add_apply]
  linarith

theorem norm_signedIntegralFunctional_le (s : SignedMeasure X) :
    ‖signedIntegralFunctional s‖ ≤ signedVariationNorm s := by
  have hb (μ : Measure X) [IsFiniteMeasure μ] : ‖continuousIntegralFunctional X μ‖ ≤ μ.real univ := by
    have hn := norm_integralDensityFunctional_le μ (fun _ => (1 : ℝ)) (integrable_const 1)
    simpa only [continuousIntegralFunctional, norm_one, integral_const, smul_eq_mul, mul_one] using hn
  change ‖continuousIntegralFunctional X s.toJordanDecomposition.posPart -
    continuousIntegralFunctional X s.toJordanDecomposition.negPart‖ ≤ _
  refine (norm_sub_le (continuousIntegralFunctional X s.toJordanDecomposition.posPart)
    (continuousIntegralFunctional X s.toJordanDecomposition.negPart)).trans ?_
  change _ ≤ (s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart).real univ
  rw [measureReal_add_apply]
  exact add_le_add (hb _) (hb _)

theorem signedVariationNorm_eq_dual_norm [Nonempty X] (s : SignedMeasure X) :
    signedVariationNorm s = ‖signedIntegralFunctional s‖ := by
  obtain ⟨μ, ν, hμ, hν, hrep, hnorm⟩ := continuousFunctional_riesz_difference_norm (signedIntegralFunctional s)
  letI := hμ
  letI := hν
  have hs : s = μ.toSignedMeasure - ν.toSignedMeasure := by
    apply signedIntegralFunctional_injective
    rw [signedIntegralFunctional_of_difference]
    ext g
    simpa only [ContinuousLinearMap.sub_apply, continuousIntegralFunctional_apply] using hrep g
  exact le_antisymm ((signedVariationNorm_le_of_difference s μ ν hs).trans_eq hnorm)
    (norm_signedIntegralFunctional_le s)

theorem abs_signed_apply_le_variation (s : SignedMeasure X) (v : Set X) :
    |s v| ≤ signedVariationNorm s := by
  by_cases hv : MeasurableSet v
  · have hs := congrArg (fun m : SignedMeasure X => m v) (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
    simp only [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hv] at hs
    rw [← hs]
    change _ ≤ (s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart).real univ
    rw [measureReal_add_apply]
    have hp := measureReal_mono (μ := s.toJordanDecomposition.posPart) (subset_univ v)
    have hn := measureReal_mono (μ := s.toJordanDecomposition.negPart) (subset_univ v)
    have hp0 : 0 ≤ s.toJordanDecomposition.posPart.real v := ENNReal.toReal_nonneg
    have hn0 : 0 ≤ s.toJordanDecomposition.negPart.real v := ENNReal.toReal_nonneg
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [VectorMeasure.not_measurable s hv, abs_zero]
    exact signedVariationNorm_nonneg s

theorem exists_signedRieszMeasure [Nonempty X] (L : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ s : SignedMeasure X, signedIntegralFunctional s = L := by
  obtain ⟨μ, ν, hμ, hν, hrep⟩ := continuousFunctional_riesz_difference L
  letI := hμ
  letI := hν
  refine ⟨μ.toSignedMeasure - ν.toSignedMeasure, ?_⟩
  rw [signedIntegralFunctional_of_difference]
  ext g
  simpa only [ContinuousLinearMap.sub_apply, continuousIntegralFunctional_apply] using (hrep g).symm

def signedRieszMeasure [Nonempty X] (L : C(X, ℝ) →L[ℝ] ℝ) : SignedMeasure X :=
  (exists_signedRieszMeasure L).choose

@[simp]
theorem signedRieszMeasure_represents [Nonempty X] (L : C(X, ℝ) →L[ℝ] ℝ) :
    signedIntegralFunctional (signedRieszMeasure L) = L :=
  (exists_signedRieszMeasure L).choose_spec

theorem signedRieszMeasure_sub [Nonempty X] (L M : C(X, ℝ) →L[ℝ] ℝ) :
    signedRieszMeasure (L - M) = signedRieszMeasure L - signedRieszMeasure M := by
  apply signedIntegralFunctional_injective
  simp only [signedIntegralFunctional_sub, signedRieszMeasure_represents]

theorem signedRieszMeasure_variation_distance [Nonempty X] (L M : C(X, ℝ) →L[ℝ] ℝ) :
    signedVariationNorm (signedRieszMeasure L - signedRieszMeasure M) = ‖L - M‖ := by
  rw [signedVariationNorm_eq_dual_norm, signedIntegralFunctional_sub,
    signedRieszMeasure_represents, signedRieszMeasure_represents]

theorem signedRieszMeasure_totalVariation_tendsto [Nonempty X]
    {ι : Type*} {l : Filter ι} {L : ι → C(X, ℝ) →L[ℝ] ℝ} {M : C(X, ℝ) →L[ℝ] ℝ}
    (hL : Tendsto L l (𝓝 M)) :
    Tendsto (fun i => signedVariationNorm (signedRieszMeasure (L i) - signedRieszMeasure M)) l (𝓝 0) := by
  simp only [signedRieszMeasure_variation_distance]
  have hsub : Tendsto (fun i => L i - M) l (𝓝 (0 : C(X, ℝ) →L[ℝ] ℝ)) := by
    simpa only [sub_self] using hL.sub_const M
  have hn := ((continuous_norm (E := C(X, ℝ) →L[ℝ] ℝ)).tendsto
    (0 : C(X, ℝ) →L[ℝ] ℝ)).comp hsub
  simpa only [Function.comp_def, norm_zero (E := C(X, ℝ) →L[ℝ] ℝ)] using hn

theorem signed_absoluteContinuity_closed_under_variation_limits
    {ι : Type*} {l : Filter ι} [l.NeBot] (s : ι → SignedMeasure X) (t : SignedMeasure X)
    (ν : Measure X) (hac : ∀ᶠ i in l, (s i).totalVariation ≪ ν)
    (hlim : Tendsto (fun i => signedVariationNorm (s i - t)) l (𝓝 0)) :
    t.totalVariation ≪ ν := by
  have hequiv : t ≪ᵥ ν.toENNRealVectorMeasure ↔ t.totalVariation ≪ ν := by
    simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using
      SignedMeasure.absolutelyContinuous_ennreal_iff t ν.toENNRealVectorMeasure
  apply hequiv.mp
  refine VectorMeasure.AbsolutelyContinuous.mk (fun v hv hνv => ?_)
  rw [Measure.toENNRealVectorMeasure_apply_measurable hv] at hνv
  have hzero : ∀ᶠ i in l, s i v = 0 := by
    filter_upwards [hac] with i hi
    exact SignedMeasure.null_of_totalVariation_zero _ (hi hνv)
  have ht : Tendsto (fun i => |(s i - t) v|) l (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun i => abs_signed_apply_le_variation (s i - t) v) hlim
  have heq : (fun i => |(s i - t) v|) =ᶠ[l] (fun _ => |t v|) := by
    filter_upwards [hzero] with i hi
    simp only [VectorMeasure.sub_apply, hi, zero_sub, abs_neg]
  have hc : Tendsto (fun _ : ι => |t v|) l (𝓝 0) := (tendsto_congr' heq).mp ht
  exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hc)

end

end GlobalRegularization
