import GlobalRegularization.ShellIsotopy

/-! Shell observation identities and isotopy with varying Banach
observation ranges, including infinite-dimensional Hilbert products. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  {Z : ℕ → Type*} [∀ j, NormedAddCommGroup (Z j)] [∀ j, NormedSpace ℝ (Z j)]

theorem shellCoordinate_general_observation_identity
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x)))
    (O : ∀ j, C1History h B →L[ℝ] Z j)
    (hann : ∀ j i, j ≤ i → (O j).comp (terminalCorrection h B (δ i) (hδ i)) = 0)
    (j : ℕ) :
    O j (shellCoordinate h B δ hδ f fm x) = O j x +
      ∑ i ∈ Finset.range j, -(O j (terminalShell h B δ hδ i (fm i x))) := by
  have hzero (i : ℕ) (hi : j ≤ i) (a : B) :
      O j (terminalCorrection h B (δ i) (hδ i) a) = 0 :=
    congrArg (fun T : B →L[ℝ] Z j => T a) (hann j i hi)
  have htail : ∀ i ∉ Finset.range j,
      O j (terminalShell h B δ hδ i (f x - fm i x)) = 0 := by
    intro i hi
    have hji : j ≤ i := Nat.le_of_not_gt (fun hit => hi (Finset.mem_range.mpr hit))
    simp only [terminalShell, ContinuousLinearMap.sub_apply, map_sub,
      hzero i hji, hzero (i + 1) (by omega), sub_self]
  have he : O j (terminalShellError h B δ hδ f fm x) =
      ∑ i ∈ Finset.range j, O j (terminalShell h B δ hδ i (f x - fm i x)) := by
    rw [terminalShellError, (O j).map_tsum hs, tsum_eq_sum htail]
  have htel : (∑ i ∈ Finset.range j, O j (terminalShell h B δ hδ i (f x))) =
      O j (terminalCorrection h B (δ 0) (hδ 0) (f x)) := by
    have ht := Finset.sum_range_sub'
      (fun i => O j (terminalCorrection h B (δ i) (hδ i) (f x))) j
    simpa only [terminalShell, ContinuousLinearMap.sub_apply, map_sub, hzero j le_rfl, sub_zero] using ht
  simp only [shellCoordinate, map_add, map_sub, he, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [htel]
  abel

theorem shellCoordinate_general_injective
    {U : Set (C1History h B)} {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (O : ∀ j, C1History h B →L[ℝ] Z j)
    (hann : ∀ j i, j ≤ i → (O j).comp (terminalCorrection h B (δ i) (hδ i)) = 0)
    (hfactor : ∀ i x y, O i x = O i y → fm i x = fm i y)
    (hsep : ∀ x y, (∀ j, O j x = O j y) → x = y) :
    Set.InjOn (shellCoordinate h B δ hδ f fm) U := by
  apply triangular_injective_on U (shellCoordinate h B δ hδ f fm) (fun j => O j) fm
    (fun j i a => -(O j (terminalShell h B δ hδ i a)))
  · intro j x hx
    exact shellCoordinate_general_observation_identity h B δ hδ f fm x
      (terminalShellError_summable h B happrox δ hδ hstep C hC hQ hx) O hann j
  · intro i x y hx hy hxy
    exact hfactor i x y hxy
  · intro x y hx hy hxy
    exact hsep x y hxy

theorem shellCoordinate_general_isotopy
    {U : Set (C1History h B)} (hU : IsOpen U)
    {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (hf : ContDiffOn ℝ 1 f U) (hfm : ∀ i, ContDiff ℝ 1 (fm i))
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (O : ∀ j, C1History h B →L[ℝ] Z j)
    (hobs : ∀ j i, j ≤ i → (O j).comp (terminalCorrection h B (δ i) (hδ i)) = 0)
    (hfactor : ∀ i x y, O i x = O i y → fm i x = fm i y)
    (hsep : ∀ x y, (∀ j, O j x = O j y) → x = y)
    (hann : ∀ i j, i ≤ j → ∀ x ∈ U,
      (fderiv ℝ (fm i) x).comp (terminalCorrection h B (δ j) (hδ j)) = 0) :
    ContDiffOn ℝ 1 (fun p : ℝ × C1History h B =>
      affineHomotopy (shellCoordinate h B δ hδ f fm) p.1 p.2) (univ.prod U) ∧
    ∀ s : ℝ, ∃ chart : C1Straightening U (endpointDerivative h B) (fun x => s • f x),
      chart.forward = affineHomotopy (shellCoordinate h B δ hδ f fm) s := by
  let A := shellCoordinate h B δ hδ f fm
  obtain ⟨hA, hdA⟩ := shellCoordinate_C1 h B hU hf hfm happrox δ hδ hstep C hC hQ
  refine ⟨affineHomotopy_joint_C1 hA, ?_⟩
  intro s
  have htri : ∀ j x, x ∈ U → O j (A x) = O j x +
      ∑ i ∈ Finset.range j, -(O j (terminalShell h B δ hδ i (fm i x))) := by
    intro j x hx
    exact shellCoordinate_general_observation_identity h B δ hδ f fm x
      (terminalShellError_summable h B happrox δ hδ hstep C hC hQ hx) O hobs j
  have hinj : Set.InjOn (affineHomotopy A s) U := by
    apply triangular_injective_on U (affineHomotopy A s) (fun j => O j) fm
      (fun j i a => s • -(O j (terminalShell h B δ hδ i a)))
    · intro j x hx
      simp only [affineHomotopy, map_add, map_smul, map_sub, htri j x hx,
        add_sub_cancel_left, Finset.smul_sum]
    · intro i x y hx hy hxy
      exact hfactor i x y hxy
    · intro x y hx hy hxy
      exact hsep x y hxy
  have hlim : ∀ x ∈ U, Tendsto (triangularPartial
      (fun i => terminalCorrection h B (δ i) (hδ i))
      (triangularDifferences (fun i => fderiv ℝ (fm i) x))) atTop (𝓝 (fderiv ℝ A x - 1)) := by
    intro x hx
    rw [(hdA x hx).fderiv]
    exact shellCoordinateDerivative_triangular_limit h B happrox δ hδ hstep C hC hQ hx
  have hdiff := affineHomotopy_invertible_derivative hU hA
    (fun i => terminalCorrection h B (δ i) (hδ i))
    (fun x => triangularDifferences (fun i => fderiv ℝ (fm i) x))
    (fun x hx => triangularDifferences_annihilation _ _ (fun i j hij => hann i j hij x hx)) hlim s
  have hAs : ContDiffOn ℝ 1 (affineHomotopy A s) U :=
    contDiffOn_id.add (contDiffOn_const.smul (hA.sub contDiffOn_id))
  have hdefect : ∀ x ∈ U, endpointDerivative h B (affineHomotopy A s x) =
      endpointDerivative h B x - s • f x := by
    intro x hx
    have he := shellCoordinate_endpoint_identity h B δ hδ f fm x
      (terminalShellError_summable h B happrox δ hδ hstep C hC hQ hx)
    change endpointDerivative h B x + s • (endpointDerivative h B (A x) - endpointDerivative h B x) = _
    rw [he]
    module
  exact ⟨straighteningOfInjectiveDerivative hU hAs hinj hdiff hdefect, rfl⟩

end

end GlobalRegularization
