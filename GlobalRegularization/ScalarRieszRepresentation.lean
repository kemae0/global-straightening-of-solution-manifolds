import GlobalRegularization.PositiveFunctionalDecomposition
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! Riesz representation of a real continuous functional on a compact
space as the difference of integrals against two finite positive Borel
measures. Positivity is constructed, rather than assumed of the input. -/

namespace GlobalRegularization

open Set MeasureTheory
open scoped CompactlySupported

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

def positiveFunctionalCompact (P : C(X, ℝ) →ₚ[ℝ] ℝ) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap :=
    { toFun := fun f => P f.toContinuousMap
      map_add' := fun f g => P.map_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => P.map_smul c f.toContinuousMap }
  monotone' := fun _ _ hfg => P.monotone (fun x => hfg x)

theorem positiveFunctional_riesz_finite (P : C(X, ℝ) →ₚ[ℝ] ℝ) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂μ = P f := by
  let Pc := positiveFunctionalCompact P
  let μ := RealRMK.rieszMeasure Pc
  have hfinite : IsFiniteMeasure μ := by
    constructor
    change (rieszContent (CompactlySupportedContinuousMap.toNNRealLinear Pc)).measure univ < ⊤
    rw [Content.measure_apply _ MeasurableSet.univ]
    exact Content.outerMeasure_lt_top_of_isCompact _ isCompact_univ
  refine ⟨μ, hfinite, ?_⟩
  intro f
  let fc : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure Pc fc

theorem continuousFunctional_riesz_difference [Nonempty X] (L : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
      ∀ f : C(X, ℝ), L f = (∫ x, f x ∂μ) - ∫ x, f x ∂ν := by
  obtain ⟨P, N, hPN⟩ := exists_positive_functional_decomposition L
  obtain ⟨μ, hμ, hP⟩ := positiveFunctional_riesz_finite P
  obtain ⟨ν, hν, hN⟩ := positiveFunctional_riesz_finite N
  exact ⟨μ, ν, hμ, hν, fun f => by rw [hP, hN]; exact hPN f⟩

theorem continuousFunctional_riesz_difference_norm [Nonempty X] (L : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
      (∀ f : C(X, ℝ), L f = (∫ x, f x ∂μ) - ∫ x, f x ∂ν) ∧
      μ.real univ + ν.real univ = ‖L‖ := by
  obtain ⟨P, N, hPN, hnorm⟩ := exists_positive_functional_decomposition_bounded L
  obtain ⟨μ, hμ, hP⟩ := positiveFunctional_riesz_finite P
  obtain ⟨ν, hν, hN⟩ := positiveFunctional_riesz_finite N
  letI := hμ
  letI := hν
  refine ⟨μ, ν, hμ, hν, fun f => by rw [hP, hN]; exact hPN f, ?_⟩
  have hp := hP (1 : C(X, ℝ))
  have hn := hN (1 : C(X, ℝ))
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at hp hn
  rw [hp, hn]
  exact hnorm

end

end GlobalRegularization
