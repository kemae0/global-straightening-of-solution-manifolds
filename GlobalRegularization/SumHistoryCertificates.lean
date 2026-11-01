import GlobalRegularization.SumHistoryNorm
import GlobalRegularization.CoordinateTransport
import GlobalRegularization.RevisedMainTheorems
import GlobalRegularization.HilbertExistence
import GlobalRegularization.FiniteNormCertificate

/-! The main spatial, spectral and isotopy conclusions on the actual
sum-norm history space specified by the revised manuscript. -/

namespace GlobalRegularization

open Set TopologicalSpace
open scoped NNReal

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

structure SumLocalizedStraightening
    (U : Set (SumC1History h B)) (f : SumC1History h B → B) (τ ε : ℝ)
    extends C1Straightening U (sumEndpointDerivative h B) f where
  preserves_zero : ∀ x ∈ U, sumHistoryInclusion h B (forward x) (historyRight h) = sumHistoryInclusion h B x (historyRight h)
  localized : ∀ x ∈ U, ∀ t : HistoryInterval h, (t : ℝ) ≤ -τ →
    sumHistoryInclusion h B (forward x) t = sumHistoryInclusion h B x t
  positive_uniform_bound : ∃ c ∈ Ioo (0 : ℝ) ε, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ U,
    ‖sumHistoryInclusion h B (affineHomotopy forward s x - x)‖ ≤ c

def sumLocalizedTransport {U : Set (SumC1History h B)} {f : SumC1History h B → B} {τ ε : ℝ}
    (s : LocalizedHistoryStraightening h B ((sumHistoryEquiv h B).symm ⁻¹' U)
      (fun y => f ((sumHistoryEquiv h B).symm y)) τ ε) (hε : 0 < ε) :
    SumLocalizedStraightening h B U f τ ε := by
  let T := sumHistoryEquiv h B
  let chart := C1Straightening.linear_transport T U (endpointDerivative h B) f s.toC1Straightening
  have hTx (x : SumC1History h B) (hx : x ∈ U) : T x ∈ T.symm ⁻¹' U := by
    simpa only [mem_preimage, T.symm_apply_apply] using hx
  refine { toC1Straightening := chart, preserves_zero := ?_, localized := ?_, positive_uniform_bound := ?_ }
  · intro x hx
    change historyInclusion h B (T (T.symm (s.forward (T x)))) (historyRight h) = _
    rw [T.apply_symm_apply]
    exact s.preserves_zero (T x) (hTx x hx)
  · intro x hx t ht
    change historyInclusion h B (T (T.symm (s.forward (T x)))) t = _
    rw [T.apply_symm_apply]
    exact s.localized (T x) (hTx x hx) t ht
  · obtain ⟨c, hc, hb⟩ := s.positive_uniform_affine_bound h B hε
    refine ⟨c, hc, ?_⟩
    intro a ha x hx
    have heq : T (affineHomotopy chart.forward a x - x) = affineHomotopy s.forward a (T x) - T x := by
      simp only [chart, C1Straightening.linear_transport, affineHomotopy, map_sub, map_add, map_smul, T.apply_symm_apply]
    change ‖historyInclusion h B (T (affineHomotopy chart.forward a x - x))‖ ≤ c
    rw [heq]
    exact hb a ha (T x) (hTx x hx)

theorem sumLocalizedTransport_certificate
    {U : Set (SumC1History h B)} (hU : IsOpen U) {f : SumC1History h B → B} {τ ε : ℝ}
    (s : LocalizedHistoryStraightening h B ((sumHistoryEquiv h B).symm ⁻¹' U)
      (fun y => f ((sumHistoryEquiv h B).symm y)) τ ε) (hε : 0 < ε)
    (hi : s.toC1Straightening.HasAffineIsotopy) (ht : s.toC1Straightening.HasTriangularDerivative) :
    (sumLocalizedTransport h B s hε).toC1Straightening.HasAffineIsotopy ∧
      (sumLocalizedTransport h B s hε).toC1Straightening.HasTriangularDerivative := by
  refine ⟨C1Straightening.linear_transport_isotopy (sumHistoryEquiv h B) U _ f s.toC1Straightening hi, ?_⟩
  apply C1Straightening.HasTriangularDerivative.conjugate s.toC1Straightening ht
    (hU.preimage (sumHistoryEquiv h B).symm.continuous) (sumHistoryEquiv h B)
    (sumLocalizedTransport h B s hε).toC1Straightening
  · intro x hx; simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hx
  · rfl

theorem HasExtendedDerivative.sum_to_max
    {U : Set (SumC1History h B)} (hU : IsOpen U) {f : SumC1History h B → B}
    (he : HasExtendedDerivative U (sumHistoryInclusion h B) f) :
    HasExtendedDerivative ((sumHistoryEquiv h B).symm ⁻¹' U) (historyInclusion h B)
      (fun y => f ((sumHistoryEquiv h B).symm y)) := by
  have hcomm : (sumHistoryInclusion h B).comp (sumHistoryEquiv h B).symm.toContinuousLinearMap =
      (ContinuousLinearMap.id ℝ (ContinuousHistory h B)).comp (historyInclusion h B) := by
    ext y t
    change historyInclusion h B ((sumHistoryEquiv h B) ((sumHistoryEquiv h B).symm y)) t = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  exact he.linear_pullback hU (sumHistoryEquiv h B).symm.toContinuousLinearMap
    (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ B) hcomm

theorem property_e_sum_finite_main
    (hh : 0 < (h : ℝ)) (n : ℕ) [NeZero n]
    (U : Set (SumC1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : SumC1History h (Fin n → ℝ) → (Fin n → ℝ))
    (he : HasExtendedDerivative U (sumHistoryInclusion h (Fin n → ℝ)) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : SumLocalizedStraightening h (Fin n → ℝ) U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
      ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  let T := sumHistoryEquiv h (Fin n → ℝ)
  letI : Nontrivial (C1History h (Fin n → ℝ)) := Function.Injective.nontrivial (historyCoordinates h (Fin n → ℝ)).symm.injective
  letI : Nontrivial (SumC1History h (Fin n → ℝ)) := Function.Injective.nontrivial T.symm.injective
  have he' := he.sum_to_max h (Fin n → ℝ) hU
  obtain ⟨s, hi, ht⟩ := terminal_atom_localized_straightening_with_triangular_derivative h hh n (T.symm ⁻¹' U)
    (hU.preimage T.symm.continuous) (fun y => f (T.symm y)) he'.c1
    (fun _ hx δ hδ hlim => property_e_terminal_limit h (Fin n → ℝ) he' δ hδ hlim hx) τ ε hτ hε
  obtain ⟨hi', ht'⟩ := sumLocalizedTransport_certificate h (Fin n → ℝ) hU s hε hi ht
  exact ⟨sumLocalizedTransport h (Fin n → ℝ) s hε, hi', fun x hx => ht'.spectrum_eq hx⟩

theorem property_e_sum_Hilbert_main
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SeparableSpace H] [Nontrivial H]
    (hh : 0 < (h : ℝ)) (U : Set (SumC1History h H)) (hU : IsOpen U) (f : SumC1History h H → H)
    (he : HasExtendedDerivative U (sumHistoryInclusion h H) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : SumLocalizedStraightening h H U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
      ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  let T := sumHistoryEquiv h H
  letI : Nontrivial (C1History h H) := Function.Injective.nontrivial (historyCoordinates h H).symm.injective
  letI : Nontrivial (SumC1History h H) := Function.Injective.nontrivial T.symm.injective
  obtain ⟨s, hi, ht⟩ := property_e_Hilbert_localized_straightening_with_certificate h H hh (T.symm ⁻¹' U)
    (hU.preimage T.symm.continuous) (fun y => f (T.symm y)) (he.sum_to_max h H hU) τ ε hτ hε
  obtain ⟨hi', ht'⟩ := sumLocalizedTransport_certificate h H hU s hε hi ht
  exact ⟨sumLocalizedTransport h H s hε, hi', fun x hx => ht'.spectrum_eq hx⟩

theorem property_e_sum_finite_dimensional [FiniteDimensional ℝ B] [Nontrivial B]
    (hh : 0 < (h : ℝ)) (U : Set (SumC1History h B)) (hU : IsOpen U) (f : SumC1History h B → B)
    (he : HasExtendedDerivative U (sumHistoryInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : SumLocalizedStraightening h B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
      ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  let T := sumHistoryEquiv h B
  letI : Nontrivial (C1History h B) := Function.Injective.nontrivial (historyCoordinates h B).symm.injective
  letI : Nontrivial (SumC1History h B) := Function.Injective.nontrivial T.symm.injective
  obtain ⟨s, hi, ht⟩ := property_e_finite_norm_certificate h B hh (T.symm ⁻¹' U)
    (hU.preimage T.symm.continuous) (fun y => f (T.symm y)) (he.sum_to_max h B hU) τ ε hτ hε
  obtain ⟨hi', ht'⟩ := sumLocalizedTransport_certificate h B hU s hε hi ht
  exact ⟨sumLocalizedTransport h B s hε, hi', fun x hx => ht'.spectrum_eq hx⟩

def sumTerminalCorrection (δ : ℝ) (hδ : 0 < δ) : B →L[ℝ] SumC1History h B :=
  (sumHistoryEquiv h B).symm.toContinuousLinearMap.comp (terminalCorrection h B δ hδ)

def SumHasVanishingTerminalDerivative (U : Set (SumC1History h B)) (f : SumC1History h B → B) : Prop :=
  ∀ x ∈ U, ∀ (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m), Filter.Tendsto δ Filter.atTop (nhds 0) →
    Filter.Tendsto (fun m => (fderiv ℝ f x).comp (sumTerminalCorrection h B (δ m) (hδ m))) Filter.atTop (nhds 0)

theorem terminal_atom_sum_finite_main
    (hh : 0 < (h : ℝ)) (n : ℕ) [NeZero n]
    (U : Set (SumC1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : SumC1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : SumHasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : SumLocalizedStraightening h (Fin n → ℝ) U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
      ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  let T := sumHistoryEquiv h (Fin n → ℝ)
  letI : Nontrivial (C1History h (Fin n → ℝ)) := Function.Injective.nontrivial (historyCoordinates h (Fin n → ℝ)).symm.injective
  letI : Nontrivial (SumC1History h (Fin n → ℝ)) := Function.Injective.nontrivial T.symm.injective
  have hf' : ContDiffOn ℝ 1 (fun y => f (T.symm y)) (T.symm ⁻¹' U) :=
    hf.comp T.symm.contDiff.contDiffOn (fun _ hy => hy)
  have hz : HasVanishingTerminalDerivative h (Fin n → ℝ) (T.symm ⁻¹' U) (fun y => f (T.symm y)) := by
    intro y hy δ hδ hlim
    have hd := (((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt le_rfl).hasFDerivAt.comp y T.symm.hasFDerivAt).fderiv
    have ht := hzero (T.symm y) hy δ hδ hlim
    simpa only [hd, ContinuousLinearMap.comp_assoc, sumTerminalCorrection] using ht
  obtain ⟨s, hi, ht⟩ := terminal_atom_localized_straightening_with_triangular_derivative h hh n (T.symm ⁻¹' U)
    (hU.preimage T.symm.continuous) _ hf' hz τ ε hτ hε
  obtain ⟨hi', ht'⟩ := sumLocalizedTransport_certificate h (Fin n → ℝ) hU s hε hi ht
  exact ⟨sumLocalizedTransport h (Fin n → ℝ) s hε, hi', fun x hx => ht'.spectrum_eq hx⟩

end

end GlobalRegularization
