import GlobalRegularization.MainStatement
import GlobalRegularization.TriangularHomotopy

/-! Every affine slice with parameter in [0,1] retains localization,
endpoint-value preservation, and the common strict displacement bound. -/

namespace GlobalRegularization

open Set
open scoped NNReal

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def LocalizedHistoryStraightening.HasLocalizedAffineIsotopy
    {U : Set (C1History h B)} {f : C1History h B → B} {τ ε : ℝ}
    (chart : LocalizedHistoryStraightening h B U f τ ε) : Prop :=
  ContDiffOn ℝ 1 (fun p : ℝ × C1History h B => affineHomotopy chart.forward p.1 p.2) (univ.prod U) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∃ slice : LocalizedHistoryStraightening h B U (fun x => s • f x) τ ε,
      slice.forward = affineHomotopy chart.forward s

theorem LocalizedHistoryStraightening.localized_isotopy_of_affine
    {U : Set (C1History h B)} {f : C1History h B → B} {τ ε : ℝ}
    (chart : LocalizedHistoryStraightening h B U f τ ε) (hε : 0 < ε)
    (hi : chart.toC1Straightening.HasAffineIsotopy) : chart.HasLocalizedAffineIsotopy h B := by
  refine ⟨hi.1, ?_⟩
  intro s hs
  obtain ⟨slice, hslice⟩ := hi.2 s
  obtain ⟨c, hc, hbound⟩ := chart.uniform_small
  let c' := max 0 c
  have hc' : 0 ≤ c' := le_max_left _ _
  have hc'ε : c' < ε := max_lt hε hc
  refine ⟨{ toC1Straightening := slice, preserves_zero := ?_, localized := ?_, uniform_small := ?_ }, hslice⟩
  · intro x hx
    rw [hslice]
    simp only [affineHomotopy, map_add, map_smul, map_sub, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.sub_apply, chart.preserves_zero x hx, sub_self, smul_zero, add_zero]
  · intro x hx t ht
    rw [hslice]
    simp only [affineHomotopy, map_add, map_smul, map_sub, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.sub_apply, chart.localized x hx t ht, sub_self, smul_zero, add_zero]
  · refine ⟨c', hc'ε, ?_⟩
    intro x hx
    rw [hslice]
    simp only [affineHomotopy, add_sub_cancel_left, map_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left ((hbound x hx).trans (le_max_right _ _)) hs.1).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 hc')

end

end GlobalRegularization
