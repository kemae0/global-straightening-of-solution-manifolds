import GlobalRegularization.SignedMeasureDuality
import GlobalRegularization.HistorySeparable
import GlobalRegularization.IntervalReferenceMeasure
import GlobalRegularization.MatrixTerminalAtom

/-! The manuscript's full-image measure argument: the derivative-coordinate
map is continuous into actual total variation, and a common finite measure
dominates every component throughout a separable family, not just a dense
subfamily. -/

namespace GlobalRegularization

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology

noncomputable section

def historyEndpointPart (h : ℝ≥0) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (L.comp (historyCoordinates h (Fin n → ℝ)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (ContinuousHistory h (Fin n → ℝ)))

def historyDerivativePart (h : ℝ≥0) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    ContinuousHistory h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (L.comp (historyCoordinates h (Fin n → ℝ)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (ContinuousHistory h (Fin n → ℝ)))

def historyScalarDerivativePart (h : ℝ≥0) (n : ℕ) (i j : Fin n)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    ContinuousHistory h ℝ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj i).comp (historyDerivativePart h n L)).comp (continuousVectorInjection n j)

def historySignedMatrix (h : ℝ≥0) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (i j : Fin n) :
    SignedMeasure (HistoryInterval h) := signedRieszMeasure (historyScalarDerivativePart h n i j L)

theorem historyScalarDerivativePart_continuous (h : ℝ≥0) (n : ℕ) (i j : Fin n) :
    Continuous (historyScalarDerivativePart h n i j) := by
  have h₀ : Continuous (fun L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L) := continuous_id
  have h₁ := h₀.clm_comp_const (historyCoordinates h (Fin n → ℝ)).symm.toContinuousLinearMap
  have h₂ := h₁.clm_comp_const (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (ContinuousHistory h (Fin n → ℝ)))
  exact (h₂.const_clm_comp (ContinuousLinearMap.proj i)).clm_comp_const (continuousVectorInjection n j)

theorem historySignedMatrix_totalVariation_continuous
    (h : ℝ≥0) (n : ℕ) (i j : Fin n) {ι : Type*} {l : Filter ι}
    (L : ι → C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (M : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hlim : Tendsto L l (𝓝 M)) :
    Tendsto (fun k => signedVariationNorm (historySignedMatrix h n (L k) i j -
      historySignedMatrix h n M i j)) l (𝓝 0) :=
  signedRieszMeasure_totalVariation_tendsto
    (((historyScalarDerivativePart_continuous h n i j).tendsto M).comp hlim)

theorem historyFunctional_signed_matrix_representation (h : ℝ≥0) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (x : C1History h (Fin n → ℝ)) (i : Fin n) :
    L x i = historyEndpointPart h n L (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
      ∑ j : Fin n, signedIntegralFunctional (historySignedMatrix h n L i j)
        (continuousVectorComponent n j (historyDerivative h (Fin n → ℝ) x)) := by
  have hsplit : L x = historyEndpointPart h n L (historyInclusion h (Fin n → ℝ) x (historyLeft h)) +
      historyDerivativePart h n L (historyDerivative h (Fin n → ℝ) x) := by
    let F := L.comp (historyCoordinates h (Fin n → ℝ)).symm.toContinuousLinearMap
    change L x = F (_, 0) + F (0, _)
    rw [← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      congrArg L ((historyCoordinates h (Fin n → ℝ)).symm_apply_apply x).symm
  have hc := congrArg (fun a : Fin n → ℝ => a i) hsplit
  change L x i = _ + _ at hc
  rw [hc]
  congr 1
  simp only [historySignedMatrix, signedRieszMeasure_represents]
  change historyDerivativePart h n L (historyDerivative h (Fin n → ℝ) x) i =
    ∑ j : Fin n, historyDerivativePart h n L
      (continuousVectorInjection n j (continuousVectorComponent n j (historyDerivative h (Fin n → ℝ) x))) i
  rw [← Finset.sum_apply, ← map_sum, continuousVector_sum_components]

theorem historySignedMatrix_endpoint_zero
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hzero : Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ)
      (adaptedTerminalWidth h m) (adaptedTerminalWidth_pos h hh m))) atTop (𝓝 0))
    (i j : Fin n) : historySignedMatrix h n L i j {historyRight h} = 0 := by
  let μ := fun i j => (historySignedMatrix h n L i j).toJordanDecomposition.posPart
  let ν := fun i j => (historySignedMatrix h n L i j).toJordanDecomposition.negPart
  have hrep (x : C1History h (Fin n → ℝ)) (i : Fin n) :
      L x i = historyEndpointPart h n L (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
        ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
          ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ν i j) := by
    simpa only [signedIntegralFunctional_apply, continuousVectorComponent_apply] using
      historyFunctional_signed_matrix_representation h n L x i
  have hatom := (matrixHistoryFunctional_terminal_zero_iff h hh n L (historyEndpointPart h n L) μ ν hrep
    (adaptedTerminalWidth h) (adaptedTerminalWidth_pos h hh) (adaptedTerminalWidth_tendsto h)).mp hzero
  have hs := congrArg (fun s : SignedMeasure (HistoryInterval h) => s {historyRight h})
    (SignedMeasure.toSignedMeasure_toJordanDecomposition (historySignedMatrix h n L i j))
  simp only [JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply (measurableSet_singleton (historyRight h))] at hs
  exact hs.symm.trans (hatom i j)

theorem exists_full_image_totalVariation_dominator
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (S : Set (C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) (hsep : IsSeparable S)
    (hzero : ∀ L ∈ S, Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ)
      (adaptedTerminalWidth h m) (adaptedTerminalWidth_pos h hh m))) atTop (𝓝 0)) :
    ∃ ν : Measure (HistoryInterval h), IsFiniteMeasure ν ∧
      ν {historyRight h} = 0 ∧
      (∀ V : Set (HistoryInterval h), IsOpen V → V.Nonempty → 0 < ν V) ∧
      ∀ L ∈ S, ∀ i j : Fin n, (historySignedMatrix h n L i j).totalVariation ≪ ν := by
  obtain ⟨s, hsS, hscount, hsclosure⟩ := hsep.exists_countable_dense_subset
  letI := hscount.to_subtype
  let M : (s × Fin n × Fin n) → SignedMeasure (HistoryInterval h) :=
    fun k => historySignedMatrix h n k.1.val k.2.1 k.2.2
  have hM (k : s × Fin n × Fin n) : M k {historyRight h} = 0 :=
    historySignedMatrix_endpoint_zero h hh n k.1.val (hzero k.1.val (hsS k.1.property)) k.2.1 k.2.2
  obtain ⟨ν, hν, hβ, hdom, hatom, hpos⟩ := exists_common_finite_signed_dominator M (historyLebesgue h)
    (historyRight h) hM (historyLebesgue_singleton h _)
  refine ⟨ν, hν, hatom, fun V hV hne => hpos V (historyLebesgue_full_support h hh V hV hne), ?_⟩
  intro L hLS i j
  obtain ⟨v, hvs, hv⟩ := mem_closure_iff_seq_limit.mp (hsclosure hLS)
  apply signed_absoluteContinuity_closed_under_variation_limits (l := atTop)
    (fun m => historySignedMatrix h n (v m) i j) (historySignedMatrix h n L i j) ν
  · exact Eventually.of_forall (fun m => hdom (⟨v m, hvs m⟩, i, j))
  · exact historySignedMatrix_totalVariation_continuous h n i j v L hv

end

end GlobalRegularization
