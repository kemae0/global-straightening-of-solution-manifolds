import GlobalRegularization.HilbertBoundedExtension
import GlobalRegularization.HilbertHistoryObservations
import GlobalRegularization.NormalizedCylindrical

/-! Genuine bounded C¹ cylindrical approximants on arbitrary open domains
of Hilbert-valued histories, with local operator-norm C¹ approximation. -/

namespace GlobalRegularization

open Set Filter Metric TopologicalSpace
open scoped NNReal Topology

noncomputable section

def observationApproximationCore {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Set E) (j : F →L[ℝ] E) (n : ℕ) : Set F :=
  {z | ‖j z‖ ≤ (n : ℝ) ∧ ∀ y : E, y ∉ U → 1 / (n + 1 : ℝ) ≤ dist (j z) y}

theorem observationApproximationCore_isClosed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Set E) (j : F →L[ℝ] E) (n : ℕ) :
    IsClosed (observationApproximationCore U j n) := by
  have hn : IsClosed {z : F | ‖j z‖ ≤ (n : ℝ)} := isClosed_le j.continuous.norm continuous_const
  have hs : IsClosed (⋂ (y : E) (_ : y ∉ U), {z : F | 1 / (n + 1 : ℝ) ≤ dist (j z) y}) :=
    isClosed_iInter (fun y => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (j.continuous.dist continuous_const)))
  have heq : observationApproximationCore U j n =
      {z : F | ‖j z‖ ≤ (n : ℝ)} ∩ ⋂ (y : E) (_ : y ∉ U), {z : F | 1 / (n + 1 : ℝ) ≤ dist (j z) y} := by
    ext z
    simp only [observationApproximationCore, mem_setOf_eq, mem_inter_iff, mem_iInter]
  rw [heq]
  exact hn.inter hs

theorem observationApproximationCore_subset {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Set E) (j : F →L[ℝ] E) (n : ℕ) :
    observationApproximationCore U j n ⊆ j ⁻¹' U := by
  intro z hz
  by_contra hnot
  have ht := hz.2 (j z) hnot
  rw [dist_self] at ht
  have hp : 0 < 1 / (n + 1 : ℝ) := by positivity
  linarith

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]

instance hilbertObservation_separable (n : ℕ) : SeparableSpace (HilbertHistoryObservationSpace H n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 2) => H)).symm.toHomeomorph.isQuotientMap.separableSpace

theorem property_e_Hilbert_bounded_C1_approximants
    (U : Set (C1History 1 H)) (hU : IsOpen U) (f : C1History 1 H → H)
    (he : HasExtendedDerivative U (historyInclusion 1 H) f) :
    ∃ fm : ℕ → C1History 1 H → H,
      (∀ n, ContDiff ℝ 1 (fm n)) ∧ (∀ n, Bornology.IsBounded (range (fm n))) ∧
      LocalC1Approximation U f fm ∧
      ∀ i x y, hilbertHistoryObservation H i x = hilbertHistoryObservation H i y → fm i x = fm i y := by
  let J := hilbertHistoryReconstruction H
  let O := hilbertHistoryObservation H
  let P := unitHistoryBernsteinCLM H
  have hJO (n : ℕ) (x : C1History 1 H) : J n (O n x) = P n x :=
    congrArg (fun L : C1History 1 H →L[ℝ] C1History 1 H => L x) (hilbertHistory_reconstruction_observation H n)
  have hpieces (n : ℕ) : ∃ g : HilbertHistoryObservationSpace H n → H,
      ContDiff ℝ 1 g ∧ Bornology.IsBounded (range g) ∧
      ∀ z ∈ observationApproximationCore U (J n) n, ‖f (J n z)‖ ≤ (n + 1 : ℝ) / 2 → g z = f (J n z) := by
    exact exists_bounded_Hilbert_C1_extension_near_closed
      (observationApproximationCore_isClosed U (J n) n) (hU.preimage (J n).continuous)
      (observationApproximationCore_subset U (J n) n) (fun z => f (J n z))
      (he.c1.comp (J n).contDiff.contDiffOn (fun z hz => hz)) (n + 1 : ℝ) (by positivity)
  choose g hg hgb hagree using hpieces
  let fm := fun n x => g n (O n x)
  have hfm (n : ℕ) : ContDiff ℝ 1 (fm n) := (hg n).comp (O n).contDiff
  have hfmb (n : ℕ) : Bornology.IsBounded (range (fm n)) :=
    (hgb n).subset (by rintro y ⟨x, rfl⟩; exact ⟨O n x, rfl⟩)
  have hlocal : ∀ x ∈ U, ∃ r > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x r, fm n y = f (P n y) := by
    intro x hx
    obtain ⟨r₀, hr₀, N₀, hcore⟩ := approximationCore_eventually_captures_ball P
      (norm_unitHistoryBernsteinCLM_le H) (unitHistoryBernstein_strong H) hU hx
    have hfc := he.c1.continuousOn.continuousAt (hU.mem_nhds hx)
    have hval := hfc.tendsto.comp (linearApprox_joint_tendsto P
      (norm_unitHistoryBernsteinCLM_le H) (unitHistoryBernstein_strong H) x)
    have hv : ∀ᶠ p : ℕ × C1History 1 H in atTop ×ˢ 𝓝 x,
        ‖f (P p.1 p.2)‖ < ‖f x‖ + 1 :=
      hval.norm.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨r₁, hr₁, N₁, hvalbound⟩ := eventually_prod_has_ball hv
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * (‖f x‖ + 1))
    refine ⟨min r₀ r₁, lt_min hr₀ hr₁, max N₀ (max N₁ N₂), ?_⟩
    intro n hn y hy
    have hyd : dist y x < min r₀ r₁ := hy
    have hy₀ : y ∈ ball x r₀ := hyd.trans_le (min_le_left _ _)
    have hy₁ : y ∈ ball x r₁ := hyd.trans_le (min_le_right _ _)
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_right N₀ _).trans hn)
    have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans ((le_max_right N₀ _).trans hn)
    have hnorm : ‖f (J n (O n y))‖ ≤ (n + 1 : ℝ) / 2 := by
      rw [hJO]
      have hvy := hvalbound n hn₁ y hy₁
      have hnn : (N₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₂
      linarith
    have hmem : O n y ∈ observationApproximationCore U (J n) n := by
      have hc := hcore n hn₀ y hy₀
      change ‖P n y‖ ≤ (n : ℝ) ∧ ∀ z, z ∉ U → 1 / (n + 1 : ℝ) ≤ dist (P n y) z at hc
      simpa only [observationApproximationCore, mem_setOf_eq, hJO] using hc
    rw [show fm n y = g n (O n y) from rfl, hagree n _ hmem hnorm, hJO]
  refine ⟨fm, hfm, hfmb, ?_, ?_⟩
  · exact localC1Approximation_of_agreement hU f he.c1 P (norm_unitHistoryBernsteinCLM_le H)
      (unitHistoryBernstein_strong H) (fun x hx => property_e_unitHistoryBernstein_derivative_approximation H he hx) fm hlocal
  · intro i x y hxy
    exact congrArg (g i) hxy

end

end GlobalRegularization
