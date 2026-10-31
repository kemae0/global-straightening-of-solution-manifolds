import GlobalRegularization.BoundaryLayer
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded

/-! Scaling of the actual terminal profiles and the uniform `C¹`
operator bound needed for the shell construction. -/

namespace GlobalRegularization

open scoped NNReal Topology

noncomputable section

theorem terminalBump_scale (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    terminalBump δ hδ t = terminalBump 1 zero_lt_one (t / δ) := by
  simp only [ContDiffBump.apply, terminalBump, sub_zero, smul_eq_mul]
  have hr : (δ / 2) / (δ / 4) = ((1 : ℝ) / 2) / (1 / 4) := by
    field_simp [hδ.ne']
  have ha : (δ / 4)⁻¹ * t = ((1 : ℝ) / 4)⁻¹ * (t / δ) := by
    field_simp [hδ.ne']
  rw [hr, ha]

theorem terminalProfile_scale (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    terminalProfile δ hδ t = δ * terminalProfile 1 zero_lt_one (t / δ) := by
  rw [terminalProfile, terminalProfile, terminalBump_scale]
  field_simp [hδ.ne']

theorem terminalProfile_deriv_scale (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (terminalProfile δ hδ) t = deriv (terminalProfile 1 zero_lt_one) (t / δ) := by
  have hd := (((terminalProfile_contDiff 1 zero_lt_one).differentiable_one (t / δ)).hasDerivAt.scomp
    t ((hasDerivAt_id t).div_const δ)).const_mul δ
  change HasDerivAt (fun s => δ * terminalProfile 1 zero_lt_one (s / δ))
    (δ * ((1 / δ) • deriv (terminalProfile 1 zero_lt_one) (t / δ))) t at hd
  have hfun : (fun s => δ * terminalProfile 1 zero_lt_one (s / δ)) = terminalProfile δ hδ :=
    funext (fun s => (terminalProfile_scale δ hδ s).symm)
  rw [hfun] at hd
  have hcoeff : δ * ((1 / δ) • deriv (terminalProfile 1 zero_lt_one) (t / δ)) =
      deriv (terminalProfile 1 zero_lt_one) (t / δ) := by
    simp [smul_eq_mul, hδ.ne']
  rw [hcoeff] at hd
  exact hd.deriv

theorem exists_terminalProfile_derivative_bound :
    ∃ M : ℝ, ∀ (δ : ℝ) (hδ : 0 < δ) (t : ℝ), ‖deriv (terminalProfile δ hδ) t‖ ≤ M := by
  have hs : HasCompactSupport (terminalProfile 1 zero_lt_one) :=
    (terminalBump 1 zero_lt_one).hasCompactSupport.mul_left
  obtain ⟨M, hM⟩ := hs.deriv.exists_bound_of_continuous
    (terminalProfile_contDiff 1 zero_lt_one).continuous_deriv_one
  exact ⟨M, fun δ hδ t => by rw [terminalProfile_deriv_scale]; exact hM (t / δ)⟩

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem exists_terminalCorrection_uniform_bound :
    ∃ C > 0, ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ‖terminalCorrection h B δ hδ‖ ≤ C := by
  obtain ⟨M, hM⟩ := exists_terminalProfile_derivative_bound
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro δ hδ hδ1
  have hq : ‖terminalScalarHistory h δ hδ‖ ≤ max 1 M := by
    change max ‖historyInclusion h ℝ (terminalScalarHistory h δ hδ)‖
      ‖historyDerivative h ℝ (terminalScalarHistory h δ hδ)‖ ≤ max 1 M
    apply max_le
    · have hv := terminalScalarHistory_small h δ hδ
      have hc := le_max_left (1 : ℝ) M
      linarith
    · apply (ContinuousMap.norm_le _ (le_trans zero_le_one (le_max_left _ _))).2
      intro t
      exact (hM δ hδ t).trans (le_max_right _ _)
  calc
    ‖terminalCorrection h B δ hδ‖ ≤ ‖terminalScalarHistory h δ hδ‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      exact norm_scalarHistoryLift_le h B (terminalScalarHistory h δ hδ)
    _ ≤ max 1 M := hq

end

end GlobalRegularization
