import GlobalRegularization.ManuscriptCutoffs
import GlobalRegularization.HilbertPaperConstruction

/-! The manuscript's actual range cutoffs and saturation formula, used to
construct the approximating family. The positive index m is encoded as n+1. -/

namespace GlobalRegularization

open Set Filter Metric Function TopologicalSpace
open scoped Topology NNReal ContDiff

noncomputable section

theorem exists_manuscript_bounded_piece
    {E F Z H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [SeparableSpace Z]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : Z ≃L[ℝ] F) (U : Set E) (hU : IsOpen U) (j : F →L[ℝ] E)
    (f : E → H) (hf : ContDiffOn ℝ 1 f U) (m : ℝ) (hm : 0 < m) :
    ∃ χ : F → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ manuscriptBelt U j m ∧
      (∀ᶠ z in 𝓝ˢ (manuscriptCore U j m), χ z = 1) ∧ (∀ z, χ z ∈ Icc 0 1) ∧
      ContDiff ℝ 1 (fun z => χ z • manuscriptHilbertSaturation m (f (j z))) ∧
      Bornology.IsBounded (range (fun z => χ z • manuscriptHilbertSaturation m (f (j z)))) ∧
      ∀ z ∈ manuscriptCore U j m, ‖f (j z)‖ ≤ m →
        χ z • manuscriptHilbertSaturation m (f (j z)) = f (j z) := by
  obtain ⟨χ, hχ, hs, hone, hr⟩ := exists_manuscript_core_cutoff e U j m hm
  refine ⟨χ, hχ, hs, hone, hr, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : j z ∈ U
    · exact (hχ.of_le (by simp)).contDiffAt.smul
        ((manuscriptHilbertSaturation_smooth m).of_le (by simp) |>.contDiffAt |>.comp z
          ((hf.contDiffAt (hU.mem_nhds hz)).comp z j.contDiff.contDiffAt))
    · have hzsup : z ∉ tsupport χ := fun ht => hz (manuscriptBelt_subset_domain U j m hm (hs ht))
      have hz0 := notMem_tsupport_iff_eventuallyEq.mp hzsup
      have hg0 : (fun y => χ y • manuscriptHilbertSaturation m (f (j y))) =ᶠ[𝓝 z] (fun _ => 0) :=
        hz0.mono (fun y hy => by simp [hy])
      exact contDiffAt_const.congr_of_eventuallyEq hg0
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨2 * m, ?_⟩
    rintro y ⟨z, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr z).1]
    exact (mul_le_mul_of_nonneg_right (hr z).2 (norm_nonneg _)).trans
      (by simpa only [one_mul] using manuscriptHilbertSaturation_bound m hm (f (j z)))
  · intro z hz hnorm
    rw [hone.self_of_nhdsSet z hz, one_smul, manuscriptHilbertSaturation_identity m hm _ hnorm]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]

theorem property_e_manuscript_Hilbert_family
    (U : Set (C1History 1 H)) (hU : IsOpen U) (f : C1History 1 H → H)
    (he : HasExtendedDerivative U (historyInclusion 1 H) f) :
    ∃ fm : ℕ → C1History 1 H → H,
      (∀ n, ContDiff ℝ 1 (fm n)) ∧ (∀ n, Bornology.IsBounded (range (fm n))) ∧
      LocalC1Approximation U f fm ∧
      ∀ i x y, paperBernstein H (i + 1) x = paperBernstein H (i + 1) y → fm i x = fm i y := by
  let P := fun n => paperBernstein H (n + 1)
  have hp (n : ℕ) : ‖P n‖ ≤ 1 := paperBernstein_contraction H _
  have hstrong (x : C1History 1 H) : Tendsto (fun n => P n x) atTop (𝓝 x) :=
    (paperBernstein_strong H x).comp (tendsto_add_atTop_nat 1)
  have hpieces (n : ℕ) := exists_manuscript_bounded_piece (paperBernsteinRangeEquiv H (n + 1))
    U hU (LinearMap.range (P n)).subtypeL f he.c1 (n + 1 : ℝ) (by positivity)
  choose χ hχ hs hone hr hg hgb hagree using hpieces
  let g := fun n (z : LinearMap.range (P n)) => χ n z • manuscriptHilbertSaturation (n + 1 : ℝ) (f z)
  let fm := fun n x => g n ((P n).rangeRestrict x)
  have hfm (n : ℕ) : ContDiff ℝ 1 (fm n) := (hg n).comp (P n).rangeRestrict.contDiff
  have hfmb (n : ℕ) : Bornology.IsBounded (range (fm n)) :=
    (hgb n).subset (by rintro y ⟨x, rfl⟩; exact ⟨(P n).rangeRestrict x, rfl⟩)
  have hlocal : ∀ x ∈ U, ∃ r > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x r, fm n y = f (P n y) := by
    intro x hx
    obtain ⟨r₀, hr₀, N₀, hcore⟩ := approximationCore_eventually_captures_ball P hp hstrong hU hx
    have hval := (he.c1.continuousOn.continuousAt (hU.mem_nhds hx)).tendsto.comp
      (linearApprox_joint_tendsto P hp hstrong x)
    obtain ⟨r₁, hr₁, N₁, hvalbound⟩ := eventually_prod_has_ball
      (hval.norm.eventually (Iio_mem_nhds (show ‖f x‖ < ‖f x‖ + 1 by linarith)))
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (‖f x‖ + 1)
    refine ⟨min r₀ r₁, lt_min hr₀ hr₁, max N₀ (max N₁ N₂), ?_⟩
    intro n hn y hy
    have hyd : dist y x < min r₀ r₁ := hy
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_right N₀ _).trans hn)
    have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans ((le_max_right N₀ _).trans hn)
    have hc := hcore n hn₀ y (hyd.trans_le (min_le_left _ _))
    have hmem : (P n).rangeRestrict y ∈ manuscriptCore U (LinearMap.range (P n)).subtypeL (n + 1 : ℝ) := by
      refine ⟨hc.1.trans (by norm_num), ?_⟩
      by_cases hu : U = univ
      · exact Or.inl hu
      · right
        exact (le_infDist (nonempty_compl.mpr hu)).mpr (fun z hz => hc.2 z hz)
    apply hagree n _ hmem
    have hv := hvalbound n hn₁ y (hyd.trans_le (min_le_right _ _))
    change ‖f (P n y)‖ < ‖f x‖ + 1 at hv
    have hnn : (N₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₂
    change ‖f (P n y)‖ ≤ (n + 1 : ℝ)
    linarith
  refine ⟨fm, hfm, hfmb, ?_, ?_⟩
  · apply localC1Approximation_of_agreement hU f he.c1 P hp hstrong _ fm hlocal
    intro x hx
    exact (property_e_unitHistoryBernstein_derivative_approximation H he hx).comp
      (paperBernsteinIndex_tendsto.comp (tendsto_add_atTop_nat 1))
  · intro i x y hxy
    apply congrArg (g i)
    exact Subtype.ext hxy

end

end GlobalRegularization
