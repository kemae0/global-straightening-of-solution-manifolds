import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! Globally bounded `C¹` extensions near compact subsets of arbitrary
open domains in finite-dimensional ranges. The cutoff is constructed by
smooth Urysohn separation and its support stays inside the open domain. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology ContDiff Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_compact_smooth_cutoff {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ, hone, hzero, hrange⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ, E)) hK.isClosed hKL
  have hsupp : Function.support χ ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hzero x hxL)
  have htsupp : tsupport χ ⊆ L := closure_minimal hsupp hL.isClosed
  have hcompact : HasCompactSupport (χ : E → ℝ) :=
    hL.of_isClosed_subset (isClosed_tsupport χ) htsupp
  exact ⟨χ, χ.contMDiff.contDiff, hcompact, htsupp.trans hLU, hone, hrange⟩

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem exists_bounded_C1_extension_near_compact
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E → B) (hf : ContDiffOn ℝ 1 f U) :
    ∃ g : E → B, ContDiff ℝ 1 g ∧ Bornology.IsBounded (Set.range g) ∧
      (∀ᶠ x in 𝓝ˢ K, g x = f x) := by
  obtain ⟨χ, hχ, hcompact, hsupport, hone, hrange⟩ := exists_compact_smooth_cutoff hK hU hKU
  let g : E → B := fun x => χ x • f x
  have hg : ContDiff ℝ 1 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by norm_num)).contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hxSupport : x ∉ tsupport χ := fun h => hx (hsupport h)
      have hzero : χ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hxSupport
      have hgz : g =ᶠ[𝓝 x] (fun _ => 0) := hzero.mono (fun y hy => by simp [g, hy])
      exact contDiffAt_const.congr_of_eventuallyEq hgz
  have hgsupport : Function.support g ⊆ tsupport χ := by
    intro x hx
    by_contra hxχ
    have hz := image_eq_zero_of_notMem_tsupport hxχ
    exact hx (by simp [g, hz])
  have hgcompact : HasCompactSupport g :=
    hcompact.of_isClosed_subset (isClosed_tsupport g) (closure_minimal hgsupport (isClosed_tsupport χ))
  refine ⟨g, hg, (hgcompact.isCompact_range hg.continuous).isBounded, ?_⟩
  exact hone.mono (fun x hx => by simp [g, hx])

end

end GlobalRegularization
