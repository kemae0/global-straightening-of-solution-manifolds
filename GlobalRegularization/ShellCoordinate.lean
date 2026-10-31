import GlobalRegularization.TerminalShellSeries
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! The actual coordinate candidate, its continuous derivative, and the
exact endpoint and remote-history identities. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def shellCoordinate (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B) :
    C1History h B :=
  x - terminalCorrection h B (δ 0) (hδ 0) (f x) + terminalShellError h B δ hδ f fm x

def shellCoordinateDerivative (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B) :
    C1History h B →L[ℝ] C1History h B :=
  ContinuousLinearMap.id ℝ _ - (terminalCorrection h B (δ 0) (hδ 0)).comp (fderiv ℝ f x) +
    ∑' i, (terminalShell h B δ hδ i).comp (fderiv ℝ f x - fderiv ℝ (fm i) x)

theorem shellCoordinate_C1
    {U : Set (C1History h B)} (hU : IsOpen U)
    {f : C1History h B → B} {fm : ℕ → C1History h B → B}
    (hf : ContDiffOn ℝ 1 f U) (hfm : ∀ i, ContDiff ℝ 1 (fm i))
    (happrox : LocalC1Approximation U f fm)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (C : ℝ) (hC : 0 < C) (hQ : ∀ i, ‖terminalCorrection h B (δ i) (hδ i)‖ ≤ C) :
    ContDiffOn ℝ 1 (shellCoordinate h B δ hδ f fm) U ∧
      ∀ x ∈ U, HasFDerivAt (shellCoordinate h B δ hδ f fm)
        (shellCoordinateDerivative h B δ hδ f fm x) x := by
  obtain ⟨hc, hd⟩ := terminalShellError_C1 h B hU hf hfm happrox δ hδ hstep C hC hQ
  constructor
  · exact (contDiffOn_id.sub ((terminalCorrection h B (δ 0) (hδ 0)).contDiff.comp_contDiffOn hf)).add hc
  · intro x hx
    have hfx := ((hf.differentiableOn le_rfl x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    exact ((hasFDerivAt_id x).sub
      ((terminalCorrection h B (δ 0) (hδ 0)).hasFDerivAt.comp x hfx)).add (hd x hx)

theorem map_terminalShellError_eq_zero
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x)))
    (L : C1History h B →L[ℝ] W)
    (hann : ∀ i, L.comp (terminalShell h B δ hδ i) = 0) :
    L (terminalShellError h B δ hδ f fm x) = 0 := by
  rw [terminalShellError, L.map_tsum hs]
  have hz : ∀ i, L (terminalShell h B δ hδ i (f x - fm i x)) = 0 := by
    intro i
    exact congrArg (fun T : B →L[ℝ] W => T (f x - fm i x)) (hann i)
  simp only [hz, tsum_zero]

theorem shellCoordinate_endpoint_identity
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x))) :
    endpointDerivative h B (shellCoordinate h B δ hδ f fm x) = endpointDerivative h B x - f x := by
  have he := map_terminalShellError_eq_zero h B δ hδ f fm x hs (endpointDerivative h B) (fun i => by
    rw [terminalShell, ContinuousLinearMap.comp_sub, terminalCorrection_endpoint,
      terminalCorrection_endpoint, sub_self])
  have hq := congrArg (fun T : B →L[ℝ] B => T (f x))
    (terminalCorrection_endpoint h B (δ 0) (hδ 0))
  simpa only [shellCoordinate, map_add, map_sub, he, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun z => endpointDerivative h B x - z) hq

theorem shellCoordinate_value_identity
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x)))
    (t : HistoryInterval h)
    (hzero : ∀ i a, historyInclusion h B (terminalCorrection h B (δ i) (hδ i) a) t = 0) :
    historyInclusion h B (shellCoordinate h B δ hδ f fm x) t = historyInclusion h B x t := by
  let L : C1History h B →L[ℝ] B := (ContinuousMap.evalCLM ℝ t).comp (historyInclusion h B)
  have hL : ∀ i, L.comp (terminalCorrection h B (δ i) (hδ i)) = 0 := by
    intro i
    apply ContinuousLinearMap.ext
    intro a
    exact hzero i a
  have he := map_terminalShellError_eq_zero h B δ hδ f fm x hs L (fun i => by
    rw [terminalShell, ContinuousLinearMap.comp_sub, hL, hL, sub_self])
  change L (shellCoordinate h B δ hδ f fm x) = L x
  rw [shellCoordinate, map_add, map_sub, he, add_zero]
  have hz : L (terminalCorrection h B (δ 0) (hδ 0) (f x)) = 0 := hzero 0 (f x)
  rw [hz, sub_zero]

theorem shellCoordinate_preserves_endpoint_value
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x))) :
    historyInclusion h B (shellCoordinate h B δ hδ f fm x) (historyRight h) =
      historyInclusion h B x (historyRight h) :=
  shellCoordinate_value_identity h B δ hδ f fm x hs (historyRight h)
    (fun i a => terminalCorrection_value_zero h B (δ i) (hδ i) a)

theorem shellCoordinate_preserves_remote_history
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (f : C1History h B → B) (fm : ℕ → C1History h B → B) (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x)))
    (τ : ℝ) (hτ : δ 0 / 2 ≤ τ) (t : HistoryInterval h) (ht : (t : ℝ) ≤ -τ) :
    historyInclusion h B (shellCoordinate h B δ hδ f fm x) t = historyInclusion h B x t := by
  apply shellCoordinate_value_identity h B δ hδ f fm x hs t
  intro i a
  apply terminalCorrection_localized h B (δ i) (hδ i) a t
  have hi := shrinkingWidths_antitone δ hδ hstep (Nat.zero_le i)
  linarith

end

end GlobalRegularization
