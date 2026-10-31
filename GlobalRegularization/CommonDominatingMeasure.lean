import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! One finite dominating measure for a countable family, preserving a
zero endpoint atom and the positivity of a full-support reference measure.
This does not yet extend domination to the full separable derivative image. -/

namespace GlobalRegularization

open Set MeasureTheory

noncomputable section

variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

omit [Countable ι] in
theorem signed_totalVariation_singleton_zero_iff [MeasurableSingletonClass X]
    (s : SignedMeasure X) (x : X) : s.totalVariation {x} = 0 ↔ s {x} = 0 := by
  constructor
  · exact s.null_of_totalVariation_zero
  · intro hs
    let j := s.toJordanDecomposition
    have hdiff : j.posPart.real {x} - j.negPart.real {x} = 0 := by
      rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s] at hs
      simpa only [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
        Measure.toSignedMeasure_apply, if_pos (measurableSet_singleton x)] using hs
    obtain ⟨u, hu, hpos, hneg⟩ := j.mutuallySingular
    have hone : j.posPart {x} = 0 ∨ j.negPart {x} = 0 := by
      by_cases hx : x ∈ u
      · exact Or.inl (measure_mono_null (singleton_subset_iff.mpr hx) hpos)
      · exact Or.inr (measure_mono_null (singleton_subset_iff.mpr hx) hneg)
    have hz : j.posPart {x} = 0 ∧ j.negPart {x} = 0 := by
      rcases hone with hp | hn
      · refine ⟨hp, ?_⟩
        have hr : (j.negPart {x}).toReal = 0 := by
          simpa only [measureReal_def, hp, ENNReal.toReal_zero, zero_sub, neg_eq_zero] using hdiff
        exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right (measure_ne_top _ _)
      · refine ⟨?_, hn⟩
        have hr : (j.posPart {x}).toReal = 0 := by
          simpa only [measureReal_def, hn, ENNReal.toReal_zero, sub_zero] using hdiff
        exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right (measure_ne_top _ _)
    change (j.posPart + j.negPart) {x} = 0
    rw [Measure.add_apply, hz.1, hz.2, add_zero]

theorem exists_common_finite_dominating_measure
    (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (β : Measure X) [IsFiniteMeasure β] (x : X)
    (hμ : ∀ i, μ i {x} = 0) (hβ : β {x} = 0) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ β ≪ ν ∧ (∀ i, μ i ≪ ν) ∧
      ν {x} = 0 ∧ (∀ s : Set X, 0 < β s → 0 < ν s) := by
  let σ := Measure.sum μ + β
  obtain ⟨ν, hν, hσν, hνσ⟩ := exists_isFiniteMeasure_absolutelyContinuous σ
  have hβσ : β ≪ σ := by
    simpa only [σ, add_comm] using
      (Measure.AbsolutelyContinuous.rfl (μ := β)).add_right (Measure.sum μ)
  have hβν := hβσ.trans hσν
  refine ⟨ν, hν, hβν, ?_, ?_, fun s hs => hβν.pos_mono hs⟩
  · intro i
    have hi : μ i ≪ Measure.sum μ := Measure.absolutelyContinuous_sum_right i Measure.AbsolutelyContinuous.rfl
    exact ((hi.add_right β).trans hσν)
  · apply hνσ
    simp only [σ, Measure.add_apply, Measure.sum_apply_of_countable, hμ, tsum_zero, hβ, add_zero]

theorem exists_common_finite_totalVariation_dominator
    (s : ι → SignedMeasure X) (β : Measure X) [IsFiniteMeasure β] (x : X)
    (hs : ∀ i, (s i).totalVariation {x} = 0) (hβ : β {x} = 0) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ β ≪ ν ∧
      (∀ i, (s i).totalVariation ≪ ν) ∧ ν {x} = 0 ∧
      (∀ u : Set X, 0 < β u → 0 < ν u) := by
  have hfinite (i : ι) : IsFiniteMeasure (s i).totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  letI := hfinite
  exact exists_common_finite_dominating_measure (fun i => (s i).totalVariation) β x hs hβ

theorem exists_common_finite_signed_dominator [MeasurableSingletonClass X]
    (s : ι → SignedMeasure X) (β : Measure X) [IsFiniteMeasure β] (x : X)
    (hs : ∀ i, s i {x} = 0) (hβ : β {x} = 0) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ β ≪ ν ∧
      (∀ i, (s i).totalVariation ≪ ν) ∧ ν {x} = 0 ∧
      (∀ u : Set X, 0 < β u → 0 < ν u) :=
  exists_common_finite_totalVariation_dominator s β x
    (fun i => (signed_totalVariation_singleton_zero_iff (s i) x).mpr (hs i)) hβ

end

end GlobalRegularization
