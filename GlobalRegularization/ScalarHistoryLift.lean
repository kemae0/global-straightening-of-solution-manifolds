import GlobalRegularization.HistorySpace

/-! Bounded linear lifts of scalar histories with Banach-space coefficients. -/

namespace GlobalRegularization

open scoped NNReal

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def scalarHistoryLift (q : C1History h ℝ) (a : B) : C1History h B :=
  historyOfClassical h B
    ⟨fun t => historyInclusion h ℝ q t • a,
      (historyInclusion h ℝ q).continuous.smul continuous_const⟩
    ⟨fun t => historyDerivative h ℝ q t • a,
      (historyDerivative h ℝ q).continuous.smul continuous_const⟩
    (fun t => (hasDerivWithinAt_value h ℝ q t).smul_const a)

@[simp]
theorem scalarHistoryLift_value (q : C1History h ℝ) (a : B) (t : HistoryInterval h) :
    historyInclusion h B (scalarHistoryLift h B q a) t = historyInclusion h ℝ q t • a := rfl

@[simp]
theorem scalarHistoryLift_derivative (q : C1History h ℝ) (a : B) (t : HistoryInterval h) :
    historyDerivative h B (scalarHistoryLift h B q a) t = historyDerivative h ℝ q t • a := rfl

theorem norm_scalarHistoryLift_le (q : C1History h ℝ) (a : B) :
    ‖scalarHistoryLift h B q a‖ ≤ ‖q‖ * ‖a‖ := by
  change max ‖historyInclusion h B (scalarHistoryLift h B q a)‖
    ‖historyDerivative h B (scalarHistoryLift h B q a)‖ ≤ ‖q‖ * ‖a‖
  apply max_le
  · apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    intro t
    rw [scalarHistoryLift_value, norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
    exact ((historyInclusion h ℝ q).norm_coe_le_norm t).trans
      (le_max_left ‖q.val.1‖ ‖q.val.2‖)
  · apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    intro t
    rw [scalarHistoryLift_derivative, norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
    exact ((historyDerivative h ℝ q).norm_coe_le_norm t).trans
      (le_max_right ‖q.val.1‖ ‖q.val.2‖)

def scalarHistoryLiftL (q : C1History h ℝ) : B →ₗ[ℝ] C1History h B where
  toFun := scalarHistoryLift h B q
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext
    · ext t; exact smul_add _ _ _
    · ext t; exact smul_add _ _ _
  map_smul' c a := by
    apply Subtype.ext
    apply Prod.ext
    · ext t; exact smul_comm _ _ _
    · ext t; exact smul_comm _ _ _

def scalarHistoryLiftCLM (q : C1History h ℝ) : B →L[ℝ] C1History h B :=
  (scalarHistoryLiftL h B q).mkContinuous ‖q‖ (norm_scalarHistoryLift_le h B q)

theorem norm_scalarHistoryLift_continuous_le (q : C1History h ℝ) (a : B) :
    ‖historyInclusion h B (scalarHistoryLiftCLM h B q a)‖ ≤
      ‖historyInclusion h ℝ q‖ * ‖a‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro t
  change ‖historyInclusion h ℝ q t • a‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right ((historyInclusion h ℝ q).norm_coe_le_norm t) (norm_nonneg a)

end

end GlobalRegularization
