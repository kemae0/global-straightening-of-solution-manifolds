import GlobalRegularization.NormalizedLocalized
import GlobalRegularization.UniformCylindricalFamily
import GlobalRegularization.TriangularDerivative

/-! The shell construction for any genuinely constructed uniformly bounded
finite-rank approximation with adjoint convergence and terminal invisibility. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem localized_straightening_of_adapted_operators_with_triangular_derivative
    (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (hf : ContDiffOn ℝ 1 f U)
    (P : ℕ → C1History h B →L[ℝ] C1History h B)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (hP : ∀ n, ‖P n‖ ≤ C₀)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hfinite : ∀ n, FiniteDimensional ℝ (LinearMap.range (P n)))
    (hfixed : ∀ x ∈ U, Tendsto (fun n => (fderiv ℝ f x).comp
      (P n - ContinuousLinearMap.id ℝ (C1History h B))) atTop (𝓝 0))
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 < σ n) (hσmono : Antitone σ)
    (hinvisible : ∀ n δ (hδ : 0 < δ), δ / 2 < σ n →
      (P n).comp (terminalCorrection h B δ hδ) = 0)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧ chart.toC1Straightening.HasTriangularDerivative := by
  obtain ⟨fm, hsmooth, hbounded, hfactor, happ⟩ :=
    exists_bounded_local_C1_cylindrical_family_uniform U hU f hf P C₀ hC₀ hP hstrong hfinite hfixed
  have hann : ∀ n δ (hδ : 0 < δ), δ / 2 < σ n → ∀ x,
      (fderiv ℝ (fm n) x).comp (terminalCorrection h B δ hδ) = 0 := by
    intro n δ hδ hshort x
    obtain ⟨hat, hhat, hfact⟩ := hfactor n
    let R := (P n).rangeRestrict
    have hzero : R.comp (terminalCorrection h B δ hδ) = 0 := by
      apply ContinuousLinearMap.ext
      intro a
      apply Subtype.ext
      exact congrArg (fun Q : B →L[ℝ] C1History h B => Q a) (hinvisible n δ hδ hshort)
    have hfun : fm n = fun y => hat (R y) := funext hfact
    have hcomp := ((hhat.differentiable_one (R x)).hasFDerivAt).comp x R.hasFDerivAt
    have hD : fderiv ℝ (fm n) x = (fderiv ℝ hat (R x)).comp R := by
      rw [hfun]
      exact hcomp.fderiv
    rw [hD, ContinuousLinearMap.comp_assoc, hzero, ContinuousLinearMap.comp_zero]
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
  let u : ℕ → ℝ := fun n => min 1 (min (1 / (n + 1 : ℝ)) (min (σ n) (min τ (b n / (M n + 1)))))
  have hu : ∀ n, 0 < u n := by
    intro n
    have hbpos : 0 < b n := by dsimp only [b]; positivity
    exact lt_min zero_lt_one (lt_min (by positivity)
      (lt_min (hσ n) (lt_min hτ (div_pos hbpos (by linarith [hM n])))))
  let δ := shrinkingWidths u
  have hδ : ∀ n, 0 < δ n := shrinkingWidths_pos u hu
  have hstep : ∀ n, δ (n + 1) ≤ δ n / 4 := shrinkingWidths_step u
  have hδu : ∀ n, δ n < u n := shrinkingWidths_lt u hu
  have hgrid (n : ℕ) : δ n ≤ 1 / (n + 1 : ℝ) :=
    (hδu n).le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hshort (n : ℕ) : δ n / 2 < σ n := by
    have hn := (hδu n).le.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hp := hδ n
    linarith
  have hremote : δ 0 / 2 ≤ τ := by
    have hn := (hδu 0).le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hp := hδ 0
    linarith
  have hbudget : ∀ i x, δ i * ‖fm i x‖ ≤ b i := by
    intro i x
    have hw : δ i ≤ b i / (M i + 1) := (hδu i).le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hm : δ i * (M i + 1) ≤ b i := (le_div_iff₀ (by linarith [hM i])).mp hw
    have hn := mul_le_mul_of_nonneg_left (hfmM i x) (hδ i).le
    have hp := hδ i
    nlinarith
  have hlim : Tendsto δ atTop (𝓝 0) :=
    squeeze_zero (fun i => (hδ i).le) hgrid tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨C, hC, hbound⟩ := exists_terminalCorrection_uniform_bound h B
  have hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C := by
    intro i
    exact hbound (δ i) (hδ i) ((hδu i).le.trans (min_le_left _ _))
  have hobs : ∀ i j, i ≤ j → (P i).comp (terminalCorrection h B (δ j) (hδ j)) = 0 := by
    intro i j hij
    exact hinvisible i (δ j) (hδ j) ((hshort j).trans_le (hσmono hij))
  have hderiv : ∀ i j, i ≤ j → ∀ x ∈ U,
      (fderiv ℝ (fm i) x).comp (terminalCorrection h B (δ j) (hδ j)) = 0 := by
    intro i j hij x hx
    exact hann i (δ j) (hδ j) ((hshort j).trans_le (hσmono hij)) x
  have hfact : ∀ i x y, P i x = P i y → fm i x = fm i y := by
    intro i x y hxy
    obtain ⟨hat, hhat, hhat_eq⟩ := hfactor i
    rw [hhat_eq x, hhat_eq y]
    exact congrArg hat (Subtype.ext hxy)
  have hinj := shellCoordinate_injective h B happ δ hδ hstep C hC hQ P hobs hfact hstrong
  have hA := (shellCoordinate_C1 h B hU hf hsmooth happ δ hδ hstep C hC hQ).1
  have hD := shellCoordinate_invertible_derivative h B hU hf hsmooth happ δ hδ hstep C hC hQ hderiv
  have hs (x : C1History h B) (hx : x ∈ U) :=
    terminalShellError_summable h B happ δ hδ hstep C hC hQ hx
  let chart := straighteningOfInjectiveDerivative hU hA hinj hD
    (fun x hx => shellCoordinate_endpoint_identity h B δ hδ f fm x (hs x hx))
  refine ⟨{ toC1Straightening := chart, preserves_zero := ?_, localized := ?_, uniform_small := ?_ }, ?_, ?_⟩
  · intro x hx
    exact shellCoordinate_preserves_endpoint_value h B δ hδ f fm x (hs x hx)
  · intro x hx t ht
    exact shellCoordinate_preserves_remote_history h B δ hδ hstep f fm x (hs x hx) τ hremote t ht
  · refine ⟨ε / 2, by linarith, ?_⟩
    intro x hx
    have ht := shellCoordinate_displacement_bound h B δ hδ hstep hlim f fm b hb.summable hbudget x (hs x hx)
    rw [hb.tsum_eq] at ht
    exact ht
  · exact shellCoordinate_isotopy h B hU hf hsmooth happ δ hδ hstep C hC hQ P hobs hfact hstrong hderiv
  · intro x hx
    refine ⟨fun i => terminalCorrection h B (δ i) (hδ i),
      triangularDifferences (fun i => fderiv ℝ (fm i) x),
      triangularDifferences_annihilation _ _ (fun i j hij => hderiv i j hij x hx), ?_⟩
    have hdA := (shellCoordinate_C1 h B hU hf hsmooth happ δ hδ hstep C hC hQ).2 x hx
    change Tendsto _ atTop (𝓝 (fderiv ℝ (shellCoordinate h B δ hδ f fm) x - 1))
    rw [hdA.fderiv]
    exact shellCoordinateDerivative_triangular_limit h B happ δ hδ hstep C hC hQ hx

theorem localized_straightening_of_adapted_operators
    (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (hf : ContDiffOn ℝ 1 f U)
    (P : ℕ → C1History h B →L[ℝ] C1History h B)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (hP : ∀ n, ‖P n‖ ≤ C₀)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hfinite : ∀ n, FiniteDimensional ℝ (LinearMap.range (P n)))
    (hfixed : ∀ x ∈ U, Tendsto (fun n => (fderiv ℝ f x).comp
      (P n - ContinuousLinearMap.id ℝ (C1History h B))) atTop (𝓝 0))
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 < σ n) (hσmono : Antitone σ)
    (hinvisible : ∀ n δ (hδ : 0 < δ), δ / 2 < σ n →
      (P n).comp (terminalCorrection h B δ hδ) = 0)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy := by
  obtain ⟨chart, hi, ht⟩ := localized_straightening_of_adapted_operators_with_triangular_derivative
    h B U hU f hf P C₀ hC₀ hP hstrong hfinite hfixed σ hσ hσmono hinvisible τ ε hτ hε
  exact ⟨chart, hi⟩

end

end GlobalRegularization
