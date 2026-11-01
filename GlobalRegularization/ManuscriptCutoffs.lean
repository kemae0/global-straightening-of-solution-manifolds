import GlobalRegularization.BernsteinRangeCutoffs
import GlobalRegularization.HilbertSaturation
import GlobalRegularization.FiniteCutoff
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! The displayed distance cores, open belts and saturation formula of
the manuscript, including the full-domain distance-to-empty exception. -/

namespace GlobalRegularization

open Set Filter Metric Function TopologicalSpace
open scoped Topology ContDiff

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def manuscriptCore (U : Set E) (j : F →L[ℝ] E) (m : ℝ) : Set F :=
  {z | ‖j z‖ ≤ m ∧ (U = univ ∨ 1 / m ≤ infDist (j z) Uᶜ)}

def manuscriptBelt (U : Set E) (j : F →L[ℝ] E) (m : ℝ) : Set F :=
  {z | ‖j z‖ < m + 1 ∧ (U = univ ∨ 1 / (2 * m) < infDist (j z) Uᶜ)}

theorem manuscriptCore_closed (U : Set E) (j : F →L[ℝ] E) (m : ℝ) : IsClosed (manuscriptCore U j m) := by
  have hn := isClosed_le j.continuous.norm (continuous_const : Continuous (fun _ : F => m))
  by_cases hu : U = univ
  · simpa only [manuscriptCore, hu, true_or, and_true] using hn
  · have hd := isClosed_le (continuous_const : Continuous (fun _ : F => 1 / m))
      ((continuous_infDist_pt Uᶜ).comp j.continuous)
    simpa only [manuscriptCore, hu, false_or, setOf_and] using hn.inter hd

theorem manuscriptBelt_open (U : Set E) (j : F →L[ℝ] E) (m : ℝ) : IsOpen (manuscriptBelt U j m) := by
  have hn := isOpen_lt j.continuous.norm (continuous_const : Continuous (fun _ : F => m + 1))
  by_cases hu : U = univ
  · simpa only [manuscriptBelt, hu, true_or, and_true] using hn
  · have hd := isOpen_lt (continuous_const : Continuous (fun _ : F => 1 / (2 * m)))
      ((continuous_infDist_pt Uᶜ).comp j.continuous)
    simpa only [manuscriptBelt, hu, false_or, setOf_and] using hn.inter hd

theorem manuscriptCore_subset_belt (U : Set E) (j : F →L[ℝ] E) (m : ℝ) (hm : 0 < m) :
    manuscriptCore U j m ⊆ manuscriptBelt U j m := by
  rintro z ⟨hn, hsep⟩
  refine ⟨hn.trans_lt (by linarith), ?_⟩
  rcases hsep with hu | hd
  · exact Or.inl hu
  · exact Or.inr ((one_div_lt_one_div_of_lt hm (by linarith : m < 2 * m)).trans_le hd)

theorem manuscriptBelt_subset_domain (U : Set E) (j : F →L[ℝ] E) (m : ℝ) (hm : 0 < m) :
    manuscriptBelt U j m ⊆ j ⁻¹' U := by
  rintro z ⟨_, hsep⟩
  rcases hsep with hu | hd
  · rw [hu]
    exact mem_univ _
  · by_contra hz
    have hzero : infDist (j z) Uᶜ = 0 := infDist_zero_of_mem hz
    rw [hzero] at hd
    have hp : 0 < 1 / (2 * m) := by positivity
    linarith

theorem manuscriptCore_compact [FiniteDimensional ℝ F]
    (U : Set E) (j : F →L[ℝ] E) (hj : ∀ z, ‖j z‖ = ‖z‖) (m : ℝ) :
    IsCompact (manuscriptCore U j m) := by
  apply (isCompact_closedBall (0 : F) m).of_isClosed_subset (manuscriptCore_closed U j m)
  intro z hz
  simpa only [mem_closedBall, dist_zero_right, ← hj z] using hz.1

theorem exists_manuscript_core_cutoff
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [SeparableSpace Z]
    (e : Z ≃L[ℝ] F) (U : Set E) (j : F →L[ℝ] E) (m : ℝ) (hm : 0 < m) :
    ∃ χ : F → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ manuscriptBelt U j m ∧
      (∀ᶠ z in 𝓝ˢ (manuscriptCore U j m), χ z = 1) ∧ ∀ z, χ z ∈ Icc 0 1 :=
  exists_smooth_cutoff_of_hilbert_equiv e (manuscriptCore_closed U j m) (manuscriptBelt_open U j m)
    (manuscriptCore_subset_belt U j m hm)

def manuscriptBeta (s : ℝ) : ℝ := scalarUnitBump (s / 4)

theorem manuscriptBeta_smooth : ContDiff ℝ ∞ manuscriptBeta :=
  scalarUnitBump.contDiff.comp (contDiff_id.div_const 4)

theorem manuscriptBeta_one (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : manuscriptBeta s = 1 := by
  apply scalarUnitBump.one_of_mem_closedBall
  change dist (s / 4) 0 ≤ 1 / 4
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hs.1 (by norm_num))]
  linarith [hs.2]

theorem manuscriptBeta_compact : HasCompactSupport manuscriptBeta := by
  apply (isCompact_closedBall (0 : ℝ) 4).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro s hs
  have hb : s / 4 ∈ support scalarUnitBump := hs
  rw [ContDiffBump.support_eq] at hb
  change dist (s / 4) 0 < 1 at hb
  have ha : |s| / 4 < 1 := by
    simpa only [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using hb
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  linarith

def manuscriptHilbertSaturation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (m : ℝ) (v : H) : H := manuscriptBeta (‖v‖ ^ 2 / m ^ 2) • v

theorem manuscriptHilbertSaturation_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (m : ℝ) (hm : 0 < m) : manuscriptHilbertSaturation (H := H) m = hilbertSaturation (2 * m) := by
  funext v
  unfold manuscriptHilbertSaturation manuscriptBeta hilbertSaturation hilbertBump
  rw [sub_zero]
  congr 2
  field_simp
  ring

theorem manuscriptHilbertSaturation_smooth
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (m : ℝ) :
    ContDiff ℝ ∞ (manuscriptHilbertSaturation (H := H) m) :=
  (manuscriptBeta_smooth.comp ((contDiff_id.norm_sq ℝ).div_const (m ^ 2))).smul contDiff_id

theorem manuscriptHilbertSaturation_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (m : ℝ) (hm : 0 < m) (v : H) : ‖manuscriptHilbertSaturation m v‖ ≤ 2 * m := by
  rw [manuscriptHilbertSaturation_eq m hm]
  exact hilbertSaturation_norm_le _ (by positivity) v

theorem manuscriptHilbertSaturation_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (m : ℝ) (hm : 0 < m) (v : H) (hv : ‖v‖ ≤ m) : manuscriptHilbertSaturation m v = v := by
  rw [manuscriptHilbertSaturation_eq m hm]
  apply hilbertSaturation_eq_self _ (by positivity) v
  linarith

end

end GlobalRegularization
