import GlobalRegularization.TerminalHistoryCutoff
import GlobalRegularization.UniformApproximationLimits
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Reconstruction of actual `C¹` history operators from derivative
operators. Uniform bounds, strong convergence, finite rank, and terminal
annihilation are derived from their concrete coordinate formula. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def historyInitialValue : C1History h B →L[ℝ] B :=
  (ContinuousMap.evalCLM ℝ (historyLeft h)).comp (historyInclusion h B)

def reconstructHistoryOperator (T : ContinuousHistory h B →L[ℝ] ContinuousHistory h B) :
    C1History h B →L[ℝ] C1History h B :=
  (historyCoordinates h B).symm.toContinuousLinearMap.comp
    ((historyInitialValue h B).prod (T.comp (historyDerivative h B)))

theorem reconstructHistoryOperator_apply (T : ContinuousHistory h B →L[ℝ] ContinuousHistory h B)
    (x : C1History h B) : reconstructHistoryOperator h B T x =
      historyReconstruct h B (historyInclusion h B x (historyLeft h)) (T (historyDerivative h B x)) := rfl

theorem norm_reconstructHistoryOperator_le
    (T : ContinuousHistory h B →L[ℝ] ContinuousHistory h B) (hT : ‖T‖ ≤ 1) :
    ‖reconstructHistoryOperator h B T‖ ≤ ‖(historyCoordinates h B).symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hv : ‖historyInclusion h B x (historyLeft h)‖ ≤ ‖x‖ :=
    ((historyInclusion h B x).norm_coe_le_norm _).trans (le_max_left _ _)
  have hd : ‖T (historyDerivative h B x)‖ ≤ ‖x‖ := by
    have ht := (T.le_opNorm (historyDerivative h B x)).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg (historyDerivative h B x)))
    exact (by simpa only [one_mul] using ht : ‖T (historyDerivative h B x)‖ ≤ ‖historyDerivative h B x‖).trans
      (le_max_right _ _)
  have hp : ‖(historyInclusion h B x (historyLeft h), T (historyDerivative h B x))‖ ≤ ‖x‖ := max_le hv hd
  exact (((historyCoordinates h B).symm : B × ContinuousHistory h B →L[ℝ] C1History h B).le_opNorm
    (historyInclusion h B x (historyLeft h), T (historyDerivative h B x))).trans
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _))

theorem reconstructHistoryOperator_strong
    (T : ℕ → ContinuousHistory h B →L[ℝ] ContinuousHistory h B)
    (hstrong : ∀ g, Tendsto (fun n => T n g) atTop (𝓝 g)) (x : C1History h B) :
    Tendsto (fun n => reconstructHistoryOperator h B (T n) x) atTop (𝓝 x) := by
  have ht := ((historyCoordinates h B).symm.continuous.tendsto
    (historyInclusion h B x (historyLeft h), historyDerivative h B x)).comp
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => historyInclusion h B x (historyLeft h)) atTop _).prodMk_nhds
      (hstrong (historyDerivative h B x)))
  have ht' : Tendsto (fun n => reconstructHistoryOperator h B (T n) x) atTop
      (𝓝 ((historyCoordinates h B).symm (historyCoordinates h B x))) := ht
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using ht'

theorem reconstructHistoryOperator_finite_range [FiniteDimensional ℝ B]
    (T : ContinuousHistory h B →L[ℝ] ContinuousHistory h B)
    [FiniteDimensional ℝ (LinearMap.range T)] :
    FiniteDimensional ℝ (LinearMap.range (reconstructHistoryOperator h B T)) := by
  let S : (B × LinearMap.range T) →L[ℝ] C1History h B :=
    (historyCoordinates h B).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ B).prodMap (LinearMap.range T).subtypeL)
  have hr : LinearMap.range (reconstructHistoryOperator h B T) ≤ LinearMap.range S := by
    rintro y ⟨x, rfl⟩
    exact ⟨(historyInclusion h B x (historyLeft h), T.rangeRestrict (historyDerivative h B x)), rfl⟩
  letI : FiniteDimensional ℝ (LinearMap.range S) :=
    inferInstanceAs (FiniteDimensional ℝ (LinearMap.range S.toLinearMap))
  exact FiniteDimensional.of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)

theorem reconstructHistoryOperator_annihilates_terminal
    (T : ContinuousHistory h B →L[ℝ] ContinuousHistory h B)
    (σ : ℝ) (hσh : σ ≤ (h : ℝ)) (δ : ℝ) (hδ : 0 < δ) (hshort : δ / 2 < σ) :
    (reconstructHistoryOperator h B (T.comp (terminalHistoryCutoff h B σ hσh))).comp
      (terminalCorrection h B δ hδ) = 0 := by
  apply ContinuousLinearMap.ext
  intro a
  rw [ContinuousLinearMap.comp_apply, reconstructHistoryOperator_apply]
  have hv : historyInclusion h B (terminalCorrection h B δ hδ a) (historyLeft h) = 0 := by
    apply terminalCorrection_localized
    change -(h : ℝ) ≤ -δ / 2
    linarith
  have hd := congrArg (fun L : B →L[ℝ] ContinuousHistory h B => L a)
    (terminalHistoryCutoff_annihilates_terminal_derivative h B σ hσh δ hδ hshort)
  change terminalHistoryCutoff h B σ hσh (historyDerivative h B (terminalCorrection h B δ hδ a)) = 0 at hd
  rw [hv, ContinuousLinearMap.comp_apply, hd, map_zero]
  exact map_zero ((historyCoordinates h B).symm : B × ContinuousHistory h B →L[ℝ] C1History h B)

omit [CompleteSpace B] in
theorem composed_contractions_strong
    (T V : ℕ → ContinuousHistory h B →L[ℝ] ContinuousHistory h B)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hstrongT : ∀ g, Tendsto (fun n => T n g) atTop (𝓝 g))
    (hstrongV : ∀ g, Tendsto (fun n => V n g) atTop (𝓝 g)) (g : ContinuousHistory h B) :
    Tendsto (fun n => (T n).comp (V n) g) atTop (𝓝 g) := by
  exact (linearApprox_joint_tendsto T hT hstrongT g).comp (tendsto_id.prodMk (hstrongV g))

end

end GlobalRegularization
