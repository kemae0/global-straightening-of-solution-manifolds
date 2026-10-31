import GlobalRegularization.ShellInvertibility
import GlobalRegularization.ShellInjectivity
import GlobalRegularization.TriangularHomotopy

/-! The manuscript's affine isotopy for the actual shell coordinate,
including global inverses for every parameter and joint `C¹` regularity. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem shellCoordinateDerivative_triangular_limit
    {U : Set (C1History h B)}
    {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    {x : C1History h B} (hx : x ∈ U) :
    Tendsto (triangularPartial (fun i => terminalCorrection h B (δ i) (hδ i))
      (triangularDifferences (fun i => fderiv ℝ (fm i) x))) atTop
      (𝓝 (shellCoordinateDerivative h B δ hδ f fm x - 1)) := by
  let Q := fun i => terminalCorrection h B (δ i) (hδ i)
  let L := fun i => fderiv ℝ (fm i) x
  let Lf := fderiv ℝ f x
  let K : C1History h B →L[ℝ] C1History h B := -(Q 0).comp Lf +
    ∑' i, (Q i - Q (i + 1)).comp (Lf - L i)
  have hcoeff := happrox.locallyVanishing_derivatives.tendsto_zero hx
  have hL : Tendsto L atTop (𝓝 Lf) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Lf) atTop (𝓝 Lf)).sub hcoeff
    simpa only [sub_sub_cancel, sub_zero, L, Lf] using ht
  have hs : Summable (fun i => (Q i - Q (i + 1)).comp (Lf - L i)) :=
    summable_linear_series_of_locally_vanishing _ (4 * C) (by positivity)
      (terminalShell_operator_max_bound h B δ hδ hstep C hC.le hQ) _
      happrox.locallyVanishing_derivatives hx
  have hK : Tendsto (shellOperatorPartial Q Lf L) atTop (𝓝 K) :=
    tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat
  have htri := triangularPartial_tendsto_of_shell Q Lf L C hC.le hQ hL K hK
  have heq : K = shellCoordinateDerivative h B δ hδ f fm x - 1 := by
    change -(Q 0).comp Lf + (∑' i, (Q i - Q (i + 1)).comp (Lf - L i)) =
      (1 : C1History h B →L[ℝ] C1History h B) - (Q 0).comp Lf +
        (∑' i, (Q i - Q (i + 1)).comp (Lf - L i)) - 1
    abel
  rw [heq] at htri
  exact htri

theorem shellCoordinate_isotopy
    {U : Set (C1History h B)} (hU : IsOpen U)
    {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (hf : ContDiffOn ℝ 1 f U) (hfm : ∀ i, ContDiff ℝ 1 (fm i))
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C)
    (O : ℕ → C1History h B →L[ℝ] C1History h B)
    (hobs : ∀ j i, j ≤ i → (O j).comp (terminalCorrection h B (δ i) (hδ i)) = 0)
    (hfactor : ∀ i x y, O i x = O i y → fm i x = fm i y)
    (hstrong : ∀ x, Tendsto (fun i => O i x) atTop (𝓝 x))
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
  have hsep : ∀ x y, x ∈ U → y ∈ U → (∀ j, O j x = O j y) → x = y := by
    intro x y hx hy hxy
    exact tendsto_nhds_unique (hstrong x) (by simpa only [hxy] using hstrong y)
  have htri : ∀ j x, x ∈ U → O j (A x) = O j x +
      ∑ i ∈ Finset.range j, -(O j (terminalShell h B δ hδ i (fm i x))) := by
    intro j x hx
    exact shellCoordinate_observation_identity h B δ hδ f fm x
      (terminalShellError_summable h B happrox δ hδ hstep C hC hQ hx) O hobs j
  have hinj := affineHomotopy_injective A O fm (fun j i a => -(O j (terminalShell h B δ hδ i a)))
    htri (fun i x y hx hy hxy => hfactor i x y hxy) hsep s
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
