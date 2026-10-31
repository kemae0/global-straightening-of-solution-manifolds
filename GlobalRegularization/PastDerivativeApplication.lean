import GlobalRegularization.RemoteTerminalCondition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The concrete past-derivative feedback example, with a localized chart
on every open history domain. The one-coordinate case is the scalar
example in the manuscript. -/

namespace GlobalRegularization

open Set
open scoped NNReal

noncomputable section

theorem pastDerivative_annihilates_terminal
    (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (t : HistoryInterval h) (ht : (t : ℝ) < 0)
    (δ : ℝ) (hδ : 0 < δ) (hshort : δ / 2 < -(t : ℝ)) :
    (historyDerivativeAt h B t).comp (terminalCorrection h B δ hδ) = 0 := by
  apply ContinuousLinearMap.ext
  intro a
  change deriv (terminalProfile δ hδ) (t : ℝ) • a = 0
  rw [terminalProfile_deriv_eq_zero_of_abs_gt δ hδ (by rwa [abs_of_neg ht]), zero_smul]

def pastDerivativeFeedback (h : ℝ≥0) (n : ℕ) (t s : HistoryInterval h)
    (x : C1History h (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => Real.sin (historyDerivative h (Fin n → ℝ) x t i) +
    (historyInclusion h (Fin n → ℝ) x s i) ^ 3

theorem pastDerivative_straightening_with_certificate
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (t s : HistoryInterval h) (ht : (t : ℝ) < 0)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U
      (pastDerivativeFeedback h n t s) τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧ chart.toC1Straightening.HasTriangularDerivative := by
  let G : ContinuousHistory h (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) :=
    fun p i => Real.sin (p.2 i) + (p.1 s i) ^ 3
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_pi.mpr
    intro i
    let e : ContinuousHistory h (Fin n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ s)
    have hv : ContDiff ℝ 1 (fun p : ContinuousHistory h (Fin n → ℝ) × (Fin n → ℝ) => p.1 s i) :=
      e.contDiff.comp contDiff_fst
    have hd : ContDiff ℝ 1 (fun p : ContinuousHistory h (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) :=
      ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ (ContinuousHistory h (Fin n → ℝ)) (Fin n → ℝ))).contDiff
    exact (Real.contDiff_sin.comp hd).add (hv.pow 3)
  obtain ⟨hf, hz⟩ := composition_terminal_condition_of_invisible h (Fin n → ℝ) (Fin n → ℝ)
    (historyDerivativeAt h (Fin n → ℝ) t) (-(t : ℝ)) (neg_pos.mpr ht)
    (fun δ hδ hshort => pastDerivative_annihilates_terminal h (Fin n → ℝ) t ht δ hδ hshort)
    univ isOpen_univ G hG.contDiffOn
  have hfall : ContDiffOn ℝ 1 (pastDerivativeFeedback h n t s) U := by
    exact hf.mono (by intro x hx; trivial)
  have hzU : HasVanishingTerminalDerivative h (Fin n → ℝ) U (pastDerivativeFeedback h n t s) :=
    fun x hx => hz x (by trivial)
  exact terminal_atom_localized_straightening_with_triangular_derivative h hh n U hU _ hfall hzU τ ε hτ hε

theorem pastDerivative_localized_straightening
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (t s : HistoryInterval h) (ht : (t : ℝ) < 0)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U
      (pastDerivativeFeedback h n t s) τ ε, chart.toC1Straightening.HasAffineIsotopy := by
  obtain ⟨chart, hi, hc⟩ := pastDerivative_straightening_with_certificate h hh n t s ht U hU τ ε hτ hε
  exact ⟨chart, hi⟩

theorem pastDerivative_full_straightening
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ) [NeZero n]
    (t s : HistoryInterval h) (ht : (t : ℝ) < 0)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U
      (pastDerivativeFeedback h n t s) τ ε, chart.toC1Straightening.HasAffineIsotopy ∧
        ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  letI : Nontrivial (C1History h (Fin n → ℝ)) :=
    Function.Injective.nontrivial (historyCoordinates h (Fin n → ℝ)).symm.injective
  obtain ⟨chart, hi, hc⟩ := pastDerivative_straightening_with_certificate h hh n t s ht U hU τ ε hτ hε
  exact ⟨chart, hi, fun x hx => hc.spectrum_eq hx⟩

end

end GlobalRegularization
