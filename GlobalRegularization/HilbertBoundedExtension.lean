import GlobalRegularization.HilbertCutoff
import GlobalRegularization.HilbertSaturation

/-! Bounded global C¹ extensions using Hilbert cutoffs and saturation.
No compactness of the input core or output range is required. -/

namespace GlobalRegularization

open Set Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {F H : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [SeparableSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem exists_bounded_Hilbert_C1_extension_near_closed
    {K U : Set F} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : F → H) (hf : ContDiffOn ℝ 1 f U) (r : ℝ) (hr : 0 < r) :
    ∃ g : F → H, ContDiff ℝ 1 g ∧ Bornology.IsBounded (range g) ∧
      ∀ z ∈ K, ‖f z‖ ≤ r / 2 → g z = f z := by
  obtain ⟨χ, hχ, hsupp, hone, hχr⟩ := exists_hilbert_C1_cutoff hK hU hKU
  let g : F → H := fun z => χ z • hilbertSaturation r (f z)
  have hg : ContDiff ℝ 1 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ U
    · exact hχ.contDiffAt.smul ((hilbertSaturation_contDiff r).contDiffAt.comp z
        (hf.contDiffAt (hU.mem_nhds hz)))
    · have hzsup : z ∉ tsupport χ := fun h => hz (hsupp h)
      have hz0 : χ =ᶠ[𝓝 z] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hzsup
      have hg0 : g =ᶠ[𝓝 z] (fun _ => 0) := hz0.mono (fun y hy => by simp [g, hy])
      exact contDiffAt_const.congr_of_eventuallyEq hg0
  refine ⟨g, hg, isBounded_iff_forall_norm_le.mpr ⟨r, ?_⟩, ?_⟩
  · rintro y ⟨z, rfl⟩
    change ‖χ z • hilbertSaturation r (f z)‖ ≤ r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχr z).1]
    exact (mul_le_mul_of_nonneg_right (hχr z).2 (norm_nonneg _)).trans
      (by simpa only [one_mul] using hilbertSaturation_norm_le r hr (f z))
  · intro z hz hnorm
    have hzχ := hone.self_of_nhdsSet z hz
    simp only [g, hzχ, one_smul, hilbertSaturation_eq_self r hr (f z) hnorm]

end

end GlobalRegularization
