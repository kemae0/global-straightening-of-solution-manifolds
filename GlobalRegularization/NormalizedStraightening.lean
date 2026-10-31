import GlobalRegularization.NormalizedCylindrical
import GlobalRegularization.ShellInvertibility
import GlobalRegularization.ShellInjectivity
import GlobalRegularization.ShrinkingWidths
import GlobalRegularization.GlobalInverse

/-! A genuine existence theorem under property (e), on the normalized
history interval and for finite-dimensional state space. The coordinate
and its inverse are constructed from the proved approximation and shell
lemmas. This theorem does not yet assert the uniform displacement bound. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B]

theorem property_e_normalized_straightening
    (U : Set (C1History 1 B)) (hU : IsOpen U) (f : C1History 1 B → B)
    (he : HasExtendedDerivative U (historyInclusion 1 B) f) (τ : ℝ) (hτ : 0 < τ) :
    ∃ chart : C1Straightening U (endpointDerivative 1 B) f,
      (∀ x ∈ U, historyInclusion 1 B (chart.forward x) (historyRight 1) =
        historyInclusion 1 B x (historyRight 1)) ∧
      ∀ x ∈ U, ∀ t : HistoryInterval 1, (t : ℝ) ≤ -τ →
        historyInclusion 1 B (chart.forward x) t = historyInclusion 1 B x t := by
  obtain ⟨fm, hsmooth, _hbounded, happ, hfactor, hann⟩ :=
    property_e_normalized_bounded_C1_approximants B B U hU f he
  let u : ℕ → ℝ := fun n => min 1 (min (1 / (n + 1 : ℝ)) τ)
  have hu : ∀ n, 0 < u n := by
    intro n
    exact lt_min zero_lt_one (lt_min (by positivity) hτ)
  let δ := shrinkingWidths u
  have hδ : ∀ n, 0 < δ n := shrinkingWidths_pos u hu
  have hstep : ∀ n, δ (n + 1) ≤ δ n / 4 := shrinkingWidths_step u
  have hδu : ∀ n, δ n < u n := shrinkingWidths_lt u hu
  have hshort (n : ℕ) : δ n / 2 < 1 / (n + 1 : ℝ) := by
    have hn := (hδu n).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hp := hδ n
    linarith
  have hremote : δ 0 / 2 ≤ τ := by
    have hn := (hδu 0).le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hp := hδ 0
    linarith
  obtain ⟨C, hC, hbound⟩ := exists_terminalCorrection_uniform_bound 1 B
  have hQ : ∀ i, ‖terminalCorrection 1 B (δ i) (hδ i)‖ ≤ C := by
    intro i
    exact hbound (δ i) (hδ i) ((hδu i).le.trans (min_le_left _ _))
  have hobs : ∀ i j, i ≤ j →
      (unitHistoryBernsteinCLM B i).comp (terminalCorrection 1 B (δ j) (hδ j)) = 0 := by
    intro i j hij
    apply unitHistoryBernstein_annihilates_terminal B i (δ j) (hδ j)
    apply (hshort j).trans_le
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hderiv : ∀ i j, i ≤ j → ∀ x ∈ U,
      (fderiv ℝ (fm i) x).comp (terminalCorrection 1 B (δ j) (hδ j)) = 0 := by
    intro i j hij x hx
    apply hann i (δ j) (hδ j)
    apply (hshort j).trans_le
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hfact : ∀ i x y, unitHistoryBernsteinCLM B i x = unitHistoryBernsteinCLM B i y →
      fm i x = fm i y := by
    intro i x y hxy
    obtain ⟨hat, hhat, hhat_eq⟩ := hfactor i
    rw [hhat_eq x, hhat_eq y]
    apply congrArg hat
    exact Subtype.ext hxy
  have hinj := shellCoordinate_injective 1 B happ δ hδ hstep C hC hQ
    (unitHistoryBernsteinCLM B) hobs hfact (unitHistoryBernstein_strong B)
  have hA := (shellCoordinate_C1 1 B hU he.c1 hsmooth happ δ hδ hstep C hC hQ).1
  have hD := shellCoordinate_invertible_derivative 1 B hU he.c1 hsmooth happ δ hδ hstep C hC hQ hderiv
  have hs (x : C1History 1 B) (hx : x ∈ U) :=
    terminalShellError_summable 1 B happ δ hδ hstep C hC hQ hx
  let chart := straighteningOfInjectiveDerivative hU hA hinj hD
    (fun x hx => shellCoordinate_endpoint_identity 1 B δ hδ f fm x (hs x hx))
  refine ⟨chart, ?_, ?_⟩
  · intro x hx
    exact shellCoordinate_preserves_endpoint_value 1 B δ hδ f fm x (hs x hx)
  · intro x hx t ht
    exact shellCoordinate_preserves_remote_history 1 B δ hδ hstep f fm x (hs x hx) τ hremote t ht

end

end GlobalRegularization
