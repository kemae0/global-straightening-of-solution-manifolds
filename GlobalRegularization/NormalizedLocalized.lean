import GlobalRegularization.NormalizedStraightening
import GlobalRegularization.ShellDisplacement
import GlobalRegularization.MainStatement
import GlobalRegularization.ShellIsotopy

/-! The full spatial straightening conclusion, including a common strict
uniform continuous-history bound, on the normalized history interval. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B]

theorem property_e_normalized_localized_straightening_with_isotopy
    (U : Set (C1History 1 B)) (hU : IsOpen U) (f : C1History 1 B → B)
    (he : HasExtendedDerivative U (historyInclusion 1 B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening 1 B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy := by
  obtain ⟨fm, hsmooth, hbounded, happ, hfactor, hann⟩ :=
    property_e_normalized_bounded_C1_approximants B B U hU f he
  have hM : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fm i x‖ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := (hbounded i).exists_norm_le
    exact ⟨max 0 M, le_max_left _ _, fun x => (hM _ (mem_range_self x)).trans (le_max_right _ _)⟩
  choose M hM hfmM using hM
  let b : ℕ → ℝ := fun n => ε / 4 * (1 / 2 : ℝ) ^ n
  have hb : HasSum b (ε / 2) := by
    have ht := HasSum.mul_left (ε / 4)
      (hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num))
    convert ht using 1
    norm_num
    ring
  let u : ℕ → ℝ := fun n => min 1 (min (1 / (n + 1 : ℝ)) (min τ (b n / (M n + 1))))
  have hu : ∀ n, 0 < u n := by
    intro n
    have hbpos : 0 < b n := by dsimp only [b]; positivity
    exact lt_min zero_lt_one (lt_min (by positivity) (lt_min hτ (div_pos hbpos (by linarith [hM n]))))
  let δ := shrinkingWidths u
  have hδ : ∀ n, 0 < δ n := shrinkingWidths_pos u hu
  have hstep : ∀ n, δ (n + 1) ≤ δ n / 4 := shrinkingWidths_step u
  have hδu : ∀ n, δ n < u n := shrinkingWidths_lt u hu
  have hgrid (n : ℕ) : δ n ≤ 1 / (n + 1 : ℝ) :=
    (hδu n).le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hshort (n : ℕ) : δ n / 2 < 1 / (n + 1 : ℝ) := by
    have hn := hgrid n
    have hp := hδ n
    linarith
  have hremote : δ 0 / 2 ≤ τ := by
    have hn := (hδu 0).le.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hp := hδ 0
    linarith
  have hbudget : ∀ i x, δ i * ‖fm i x‖ ≤ b i := by
    intro i x
    have hw : δ i ≤ b i / (M i + 1) := (hδu i).le.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hm : δ i * (M i + 1) ≤ b i := (le_div_iff₀ (by linarith [hM i])).mp hw
    have hn := mul_le_mul_of_nonneg_left (hfmM i x) (hδ i).le
    have hp := hδ i
    nlinarith
  have hlim : Tendsto δ atTop (𝓝 0) :=
    squeeze_zero (fun i => (hδ i).le) hgrid tendsto_one_div_add_atTop_nhds_zero_nat
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
    exact congrArg hat (Subtype.ext hxy)
  have hinj := shellCoordinate_injective 1 B happ δ hδ hstep C hC hQ
    (unitHistoryBernsteinCLM B) hobs hfact (unitHistoryBernstein_strong B)
  have hA := (shellCoordinate_C1 1 B hU he.c1 hsmooth happ δ hδ hstep C hC hQ).1
  have hD := shellCoordinate_invertible_derivative 1 B hU he.c1 hsmooth happ δ hδ hstep C hC hQ hderiv
  have hs (x : C1History 1 B) (hx : x ∈ U) :=
    terminalShellError_summable 1 B happ δ hδ hstep C hC hQ hx
  let chart := straighteningOfInjectiveDerivative hU hA hinj hD
    (fun x hx => shellCoordinate_endpoint_identity 1 B δ hδ f fm x (hs x hx))
  refine ⟨{ toC1Straightening := chart, preserves_zero := ?_, localized := ?_, uniform_small := ?_ }, ?_⟩
  · intro x hx
    exact shellCoordinate_preserves_endpoint_value 1 B δ hδ f fm x (hs x hx)
  · intro x hx t ht
    exact shellCoordinate_preserves_remote_history 1 B δ hδ hstep f fm x (hs x hx) τ hremote t ht
  · refine ⟨ε / 2, by linarith, ?_⟩
    intro x hx
    have ht := shellCoordinate_displacement_bound 1 B δ hδ hstep hlim f fm b hb.summable hbudget x (hs x hx)
    rw [hb.tsum_eq] at ht
    exact ht
  · exact shellCoordinate_isotopy 1 B hU he.c1 hsmooth happ δ hδ hstep C hC hQ
      (unitHistoryBernsteinCLM B) hobs hfact (unitHistoryBernstein_strong B) hderiv

theorem property_e_normalized_localized_straightening
    (U : Set (C1History 1 B)) (hU : IsOpen U) (f : C1History 1 B → B)
    (he : HasExtendedDerivative U (historyInclusion 1 B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    Nonempty (LocalizedHistoryStraightening 1 B U f τ ε) := by
  obtain ⟨chart, hisotopy⟩ := property_e_normalized_localized_straightening_with_isotopy B U hU f he τ ε hτ hε
  exact ⟨chart⟩

end

end GlobalRegularization
