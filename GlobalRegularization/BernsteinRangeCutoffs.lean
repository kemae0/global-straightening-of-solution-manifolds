import GlobalRegularization.PaperBernsteinGrids
import GlobalRegularization.HilbertCylindricalFamily

/-! Smooth cutoffs on the actual Bernstein history ranges, with the
inherited history norm, obtained through the proved Hilbert equivalence. -/

namespace GlobalRegularization

open Set Filter Function TopologicalSpace
open scoped Topology NNReal ContDiff

noncomputable section

theorem exists_smooth_cutoff_of_hilbert_equiv
    {Z E : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [SeparableSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : Z ≃L[ℝ] E)
    {K U : Set E} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨χ, hχ, hs, hone, hr⟩ := exists_hilbert_smooth_cutoff
    (hK.preimage e.continuous) (hU.preimage e.continuous) (fun z hz => hKU hz)
  refine ⟨fun x => χ (e.symm x), hχ.comp e.symm.contDiff, ?_, ?_, fun x => hr _⟩
  · have ht : tsupport (fun x => χ (e.symm x)) ⊆ e.symm ⁻¹' tsupport χ := by
      apply closure_minimal
      · intro x hx
        exact subset_closure hx
      · exact isClosed_closure.preimage e.symm.continuous
    intro x hx
    have h := hs (ht hx)
    simpa only [mem_preimage, e.apply_symm_apply] using h
  · obtain ⟨V, hV, hKV, heq⟩ := eventually_nhdsSet_iff_exists.mp hone
    apply eventually_nhdsSet_iff_exists.mpr
    refine ⟨e.symm ⁻¹' V, hV.preimage e.symm.continuous, ?_, fun x hx => heq _ hx⟩
    intro x hx
    apply hKV
    simpa only [mem_preimage, e.apply_symm_apply] using hx

theorem exists_smooth_cutoff_Bernstein_range
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    (m : ℕ) {K U : Set (LinearMap.range (paperBernstein H m))}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : LinearMap.range (paperBernstein H m) → ℝ,
      ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
        (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 :=
  exists_smooth_cutoff_of_hilbert_equiv (paperBernsteinRangeEquiv H m) hK hU hKU

end

end GlobalRegularization
