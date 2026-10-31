import GlobalRegularization.CylindricalPieces
import Mathlib.Analysis.SpecificLimits.Basic

/-! A family of globally bounded cylindrical `C¹` maps. Uniformly bounded
strongly convergent finite-rank observations eventually send a common
neighborhood into their compact cores, so the cutoffs agree exactly with
the original function composed with the observations. -/

namespace GlobalRegularization

open Set Filter Metric
open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem approximationCore_eventually_captures_ball
    (P : ℕ → E →L[ℝ] E) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ r > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x r,
      (P n).rangeRestrict y ∈ approximationCore U (LinearMap.range (P n)).subtypeL n := by
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hstrong x) (a / 4) (by positivity)
  have hwidth : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < a / 2 :=
    (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 (a / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hwidth
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (‖x‖ + 1)
  refine ⟨min 1 (a / 4), lt_min zero_lt_one (by positivity), max N₁ (max N₂ N₃), ?_⟩
  intro n hn y hy
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left N₂ N₃).trans ((le_max_right N₁ _).trans hn)
  have hn₃ : N₃ ≤ n := (le_max_right N₂ N₃).trans ((le_max_right N₁ _).trans hn)
  have hyd : dist y x < min 1 (a / 4) := hy
  have hdiff : dist (P n y) (P n x) ≤ dist y x := by
    have hm := mul_le_mul_of_nonneg_right (hP n) (dist_nonneg : 0 ≤ dist y x)
    simpa only [one_mul] using ((P n).dist_le_opNorm y x).trans hm
  have hnear : dist (P n y) x < a / 2 := by
    have ht := dist_triangle (P n y) (P n x) x
    have hxP := hN₁ n hn₁
    have hyr : dist y x < a / 4 := lt_of_lt_of_le hyd (min_le_right _ _)
    linarith
  constructor
  · change ‖P n y‖ ≤ (n : ℝ)
    have hpn : ‖P n y‖ ≤ ‖y‖ := by
      have hm := mul_le_mul_of_nonneg_right (hP n) (norm_nonneg y)
      simpa only [one_mul] using ((P n).le_opNorm y).trans hm
    have hyn : ‖y‖ ≤ ‖x‖ + dist y x := by
      calc
        ‖y‖ ≤ ‖x‖ + ‖x - y‖ := norm_le_norm_add_norm_sub x y
        _ = ‖x‖ + dist y x := by rw [dist_eq_norm, norm_sub_rev]
    have hyn1 : dist y x < 1 := lt_of_lt_of_le hyd (min_le_left _ _)
    have hnn : (N₃ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₃
    linarith
  · intro z hz
    change 1 / (n + 1 : ℝ) ≤ dist (P n y) z
    have hfar : a ≤ dist z x := by
      by_contra hfar
      exact hz (hball (by exact lt_of_not_ge hfar))
    have ht := dist_triangle z (P n y) x
    rw [dist_comm z (P n y)] at ht
    have hw := hN₂ n hn₂
    linarith

theorem exists_bounded_cylindrical_family
    (U : Set E) (hU : IsOpen U) (f : E → B) (hf : ContDiffOn ℝ 1 f U)
    (P : ℕ → E →L[ℝ] E) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hfinite : ∀ n, FiniteDimensional ℝ (LinearMap.range (P n))) :
    ∃ fm : ℕ → E → B,
      (∀ n, ContDiff ℝ 1 (fm n)) ∧ (∀ n, Bornology.IsBounded (range (fm n))) ∧
      (∀ n, ∃ hat : LinearMap.range (P n) → B, ContDiff ℝ 1 hat ∧
        ∀ x, fm n x = hat ((P n).rangeRestrict x)) ∧
      ∀ x ∈ U, ∃ r > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x r, fm n y = f (P n y) := by
  have hpieces : ∀ n, ∃ fn : E → B, ContDiff ℝ 1 fn ∧ Bornology.IsBounded (range fn) ∧
      (∃ hat : LinearMap.range (P n) → B, ContDiff ℝ 1 hat ∧ ∀ x, fn x = hat ((P n).rangeRestrict x)) ∧
      ∀ x, (P n).rangeRestrict x ∈ approximationCore U (LinearMap.range (P n)).subtypeL n → fn x = f (P n x) := by
    intro n
    letI := hfinite n
    exact exists_bounded_cylindrical_piece U hU f hf (P n) n
  choose fm hfm hbound hfactor hagree using hpieces
  refine ⟨fm, hfm, hbound, hfactor, ?_⟩
  intro x hx
  obtain ⟨r, hr, N, hcapture⟩ := approximationCore_eventually_captures_ball P hP hstrong hU hx
  exact ⟨r, hr, N, fun n hn y hy => hagree n y (hcapture n hn y hy)⟩

end

end GlobalRegularization
