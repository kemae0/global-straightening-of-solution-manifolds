import GlobalRegularization.ShellCoordinate
import GlobalRegularization.Triangular

/-! Global injectivity of the constructed coordinate from the actual
finite observation identities. Nested grids are not required. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem shellCoordinate_observation_identity
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x)))
    (O : ℕ → C1History h B →L[ℝ] C1History h B)
    (hann : ∀ j i, j ≤ i → (O j).comp (terminalCorrection h B (δ i) (hδ i)) = 0)
    (j : ℕ) :
    O j (shellCoordinate h B δ hδ f fm x) = O j x +
      ∑ i ∈ Finset.range j, -(O j (terminalShell h B δ hδ i (fm i x))) := by
  have hzero (i : ℕ) (hi : j ≤ i) (a : B) :
      O j (terminalCorrection h B (δ i) (hδ i) a) = 0 :=
    congrArg (fun T : B →L[ℝ] C1History h B => T a) (hann j i hi)
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
  simp only [shellCoordinate, map_add, map_sub, he, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  rw [htel]
  abel

theorem shellCoordinate_injective
    {U : Set (C1History h B)} {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (O : ℕ → C1History h B →L[ℝ] C1History h B)
    (hann : ∀ j i, j ≤ i → (O j).comp (terminalCorrection h B (δ i) (hδ i)) = 0)
    (hfactor : ∀ i x y, O i x = O i y → fm i x = fm i y)
    (hstrong : ∀ x, Tendsto (fun i => O i x) atTop (𝓝 x)) :
    Set.InjOn (shellCoordinate h B δ hδ f fm) U := by
  apply triangular_injective_on U (shellCoordinate h B δ hδ f fm)
    (fun i => O i) fm (fun j i a => -(O j (terminalShell h B δ hδ i a)))
  · intro j x hx
    exact shellCoordinate_observation_identity h B δ hδ f fm x
      (terminalShellError_summable h B happrox δ hδ hstep C hC hQ hx) O hann j
  · intro i x y hx hy hxy
    exact hfactor i x y hxy
  · intro x y hx hy hxy
    exact tendsto_nhds_unique (hstrong x) (by simpa only [hxy] using hstrong y)

end

end GlobalRegularization
