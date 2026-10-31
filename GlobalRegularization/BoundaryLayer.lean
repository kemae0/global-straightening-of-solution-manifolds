import GlobalRegularization.HistorySpace
import GlobalRegularization.ScalarHistoryLift
import GlobalRegularization.ExtendedDerivative
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Terminal correction profiles

Actual smooth scalar histories supported in a terminal interval, with
value zero and derivative one at the endpoint, and a small continuous
history norm. These are analytic functions, not abstract assumed maps.
-/

namespace GlobalRegularization

open Set
open scoped NNReal Topology

noncomputable section

def terminalBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) where
  rIn := δ / 4
  rOut := δ / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def terminalProfile (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  t * terminalBump δ hδ t

theorem terminalProfile_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ 1 (terminalProfile δ hδ) :=
  contDiff_id.mul (terminalBump δ hδ).contDiff

@[simp]
theorem terminalProfile_zero (δ : ℝ) (hδ : 0 < δ) : terminalProfile δ hδ 0 = 0 := by
  simp [terminalProfile]

@[simp]
theorem terminalProfile_deriv_zero (δ : ℝ) (hδ : 0 < δ) :
    deriv (terminalProfile δ hδ) 0 = 1 := by
  have hb := ((terminalBump δ hδ).contDiff (n := 1)).differentiable le_rfl
  have hi := (hasDerivAt_id (0 : ℝ)).mul (hb 0).hasDerivAt
  have hone : terminalBump δ hδ 0 = 1 :=
    (terminalBump δ hδ).one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_self]
      change 0 ≤ δ / 4
      positivity)
  simpa [terminalProfile, hone] using hi.deriv

theorem terminalProfile_eq_zero (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : t ≤ -δ / 2) : terminalProfile δ hδ t = 0 := by
  have hd : (terminalBump δ hδ).rOut ≤ dist t 0 := by
    simp only [terminalBump, Real.dist_eq, sub_zero]
    exact le_trans (by linarith) (neg_le_abs t)
  simp [terminalProfile, (terminalBump δ hδ).zero_of_le_dist hd]

theorem abs_terminalProfile_le (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    |terminalProfile δ hδ t| ≤ δ / 2 := by
  by_cases ht : δ / 2 ≤ |t|
  · have hd : (terminalBump δ hδ).rOut ≤ dist t 0 := by
      simpa only [terminalBump, Real.dist_eq, sub_zero] using ht
    simp only [terminalProfile, (terminalBump δ hδ).zero_of_le_dist hd, mul_zero, abs_zero]
    positivity
  · have hb0 := (terminalBump δ hδ).nonneg (x := t)
    have hb1 := (terminalBump δ hδ).le_one (x := t)
    calc
      |terminalProfile δ hδ t| = |t| * terminalBump δ hδ t := by
        rw [terminalProfile, abs_mul, abs_of_nonneg hb0]
      _ ≤ |t| := mul_le_of_le_one_right (abs_nonneg _) hb1
      _ ≤ δ / 2 := (not_le.mp ht).le

def terminalScalarHistory (h : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) : C1History h ℝ :=
  historyOfC1Function h ℝ (terminalProfile δ hδ) (deriv (terminalProfile δ hδ))
    (terminalProfile_contDiff δ hδ).continuous
    (terminalProfile_contDiff δ hδ).continuous_deriv_one
    (fun t => ((terminalProfile_contDiff δ hδ).differentiable le_rfl t).hasDerivAt)

@[simp]
theorem terminalScalarHistory_endpoint (h : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    endpointDerivative h ℝ (terminalScalarHistory h δ hδ) = 1 := by
  change deriv (terminalProfile δ hδ) 0 = 1
  simp

@[simp]
theorem terminalScalarHistory_value_zero (h : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    historyInclusion h ℝ (terminalScalarHistory h δ hδ) (historyRight h) = 0 := by
  change terminalProfile δ hδ 0 = 0
  simp

theorem terminalScalarHistory_localized (h : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (t : HistoryInterval h) (ht : (t : ℝ) ≤ -δ / 2) :
    historyInclusion h ℝ (terminalScalarHistory h δ hδ) t = 0 :=
  terminalProfile_eq_zero δ hδ ht

theorem terminalScalarHistory_small (h : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ‖historyInclusion h ℝ (terminalScalarHistory h δ hδ)‖ ≤ δ / 2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  exact abs_terminalProfile_le δ hδ t

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def terminalCorrection (δ : ℝ) (hδ : 0 < δ) : B →L[ℝ] C1History h B :=
  scalarHistoryLiftCLM h B (terminalScalarHistory h δ hδ)

theorem terminalCorrection_endpoint (δ : ℝ) (hδ : 0 < δ) :
    (endpointDerivative h B).comp (terminalCorrection h B δ hδ) =
      ContinuousLinearMap.id ℝ B := by
  ext a
  change endpointDerivative h ℝ (terminalScalarHistory h δ hδ) • a = a
  simp

theorem terminalCorrection_value_zero (δ : ℝ) (hδ : 0 < δ) (a : B) :
    historyInclusion h B (terminalCorrection h B δ hδ a) (historyRight h) = 0 := by
  change historyInclusion h ℝ (terminalScalarHistory h δ hδ) (historyRight h) • a = 0
  simp

theorem terminalCorrection_localized (δ : ℝ) (hδ : 0 < δ) (a : B)
    (t : HistoryInterval h) (ht : (t : ℝ) ≤ -δ / 2) :
    historyInclusion h B (terminalCorrection h B δ hδ a) t = 0 := by
  change historyInclusion h ℝ (terminalScalarHistory h δ hδ) t • a = 0
  rw [terminalScalarHistory_localized h δ hδ t ht, zero_smul]

theorem terminalCorrection_small (δ : ℝ) (hδ : 0 < δ) :
    ‖(historyInclusion h B).comp (terminalCorrection h B δ hδ)‖ ≤ δ / 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  exact (norm_scalarHistoryLift_continuous_le h B (terminalScalarHistory h δ hδ) a).trans
    (mul_le_mul_of_nonneg_right (terminalScalarHistory_small h δ hδ) (norm_nonneg a))

theorem terminalCorrection_tendsto_zero
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hlim : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => (historyInclusion h B).comp (terminalCorrection h B (δ n) (hδ n)))
      Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => terminalCorrection_small h B (δ n) (hδ n))
  simpa using hlim.div_const 2

theorem property_e_terminal_limit
    {U : Set (C1History h B)} {f : C1History h B → B}
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hlim : Filter.Tendsto δ Filter.atTop (nhds 0))
    {x : C1History h B} (hx : x ∈ U) :
    Filter.Tendsto
      (fun n => (fderiv ℝ f x).comp (terminalCorrection h B (δ n) (hδ n)))
      Filter.atTop (nhds 0) :=
  he.tendsto_derivative_comp (fun n => terminalCorrection h B (δ n) (hδ n)) hx
    (terminalCorrection_tendsto_zero h B δ hδ hlim)

end

end GlobalRegularization
