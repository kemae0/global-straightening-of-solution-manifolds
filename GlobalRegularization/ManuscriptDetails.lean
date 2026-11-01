import GlobalRegularization.TerminalExistence
import GlobalRegularization.MainExistence

/-! Explicit supplementary assertions in the manuscript: local bounds
for extended derivatives, the literal supremum estimate, and failure of
necessity of the terminal-atom hypothesis. -/

namespace GlobalRegularization

open Set Filter Metric
open scoped Topology NNReal

noncomputable section

theorem joint_linear_action_locally_bounded
    {E C B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {U : Set E} (hU : IsOpen U) (F : E → C →L[ℝ] B)
    (hF : ContinuousOn (fun p : E × C => F p.1 p.2) (U.prod univ))
    (x : E) (hx : x ∈ U) :
    ∃ r > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ ball x r, ‖F y‖ ≤ M := by
  have hc := hF.continuousAt ((hU.prod isOpen_univ).mem_nhds (show (x, (0 : C)) ∈ U.prod univ from ⟨hx, mem_univ _⟩))
  obtain ⟨r, hr, hb⟩ := Metric.continuousAt_iff.mp hc 1 zero_lt_one
  refine ⟨r / 2, by positivity, 2 / r, by positivity, ?_⟩
  intro y hy
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (f := F y) (by positivity)
  intro v hv
  have hdist : dist (y, (r / 2) • v) (x, (0 : C)) < r := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · exact (show dist y x < r / 2 from hy).trans (by linarith)
    · rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2), hv, mul_one]
      linarith
  have hi := hb hdist
  have hn : (r / 2) * ‖F y v‖ < 1 := by
    simpa only [map_zero, dist_zero_right, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < r / 2)] using hi
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem HasExtendedDerivative.exists_locally_bounded_extension
    {E C B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {U : Set E} {f : E → B} {ι : E →L[ℝ] C}
    (he : HasExtendedDerivative U ι f) (hU : IsOpen U) :
    ∃ F : E → C →L[ℝ] B,
      (∀ x ∈ U, fderiv ℝ f x = (F x).comp ι) ∧
      ContinuousOn (fun p : E × C => F p.1 p.2) (U.prod univ) ∧
      ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ ball x r, ‖F y‖ ≤ M := by
  obtain ⟨F, hder, hc⟩ := he.exists_extension
  exact ⟨F, hder, hc, fun x hx => joint_linear_action_locally_bounded hU F hc x hx⟩

theorem LocalizedHistoryStraightening.sup_displacement_lt
    (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {U : Set (C1History h B)} {f : C1History h B → B} {τ ε : ℝ}
    (chart : LocalizedHistoryStraightening h B U f τ ε) (hε : 0 < ε) :
    sSup ((fun x => ‖historyInclusion h B (chart.forward x - x)‖) '' U) < ε := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simpa only [image_empty, Real.sSup_empty] using hε
  · obtain ⟨c, hc, hb⟩ := chart.uniform_small
    apply (csSup_le (hne.image _) ?_).trans_lt hc
    rintro a ⟨x, hx, rfl⟩
    exact hb x hx

def twiceEndpointStraightening (h : ℝ≥0) :
    C1Straightening (univ : Set (C1History h ℝ)) (endpointDerivative h ℝ)
      (fun x => (2 : ℝ) • endpointDerivative h ℝ x) where
  target := univ
  target_open := isOpen_univ
  forward := fun x => -x
  backward := fun x => -x
  forward_maps := mapsTo_univ _ _
  backward_maps := mapsTo_univ _ _
  left_inverse := fun x _ => neg_neg x
  right_inverse := fun x _ => neg_neg x
  forward_smooth := contDiffOn_id.neg
  backward_smooth := contDiffOn_id.neg
  endpoint_identity := by intro x _; rw [map_neg]; module

theorem twiceEndpoint_not_terminal (h : ℝ≥0) (hh : 0 < (h : ℝ)) :
    ¬ HasVanishingTerminalDerivative h ℝ univ (fun x => (2 : ℝ) • endpointDerivative h ℝ x) := by
  intro hz
  have ht := hz 0 (mem_univ _) (adaptedTerminalWidth h) (adaptedTerminalWidth_pos h hh)
    (adaptedTerminalWidth_tendsto h)
  have hd : fderiv ℝ (fun x => (2 : ℝ) • endpointDerivative h ℝ x) 0 =
      (2 : ℝ) • endpointDerivative h ℝ :=
    (((2 : ℝ) • endpointDerivative h ℝ).hasFDerivAt).fderiv
  have heq (m : ℕ) : (fderiv ℝ (fun x => (2 : ℝ) • endpointDerivative h ℝ x) 0).comp
      (terminalCorrection h ℝ (adaptedTerminalWidth h m) (adaptedTerminalWidth_pos h hh m)) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    rw [hd, ContinuousLinearMap.smul_comp, terminalCorrection_endpoint]
  simp only [heq] at ht
  have he := tendsto_nhds_unique ht tendsto_const_nhds
  have ha := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) he
  norm_num at ha

end

end GlobalRegularization
