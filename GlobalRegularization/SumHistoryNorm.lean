import GlobalRegularization.HistorySpace
import Mathlib.Analysis.Normed.Lp.ProdLp

/-! The revised manuscript's sum norm on the genuine closed FTC graph.
The old maximum-norm space and this space are continuously linearly
equivalent, with explicit comparison constants. -/

namespace GlobalRegularization

open scoped NNReal

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def sumHistoryDefect : WithLp 1 (ContinuousHistory h B × ContinuousHistory h B) →L[ℝ] ContinuousHistory h B :=
  (historyDefect h B).comp
    (WithLp.prodContinuousLinearEquiv 1 ℝ (ContinuousHistory h B) (ContinuousHistory h B)).toContinuousLinearMap

def SumC1History := ↥(LinearMap.ker (sumHistoryDefect h B))

instance : NormedAddCommGroup (SumC1History h B) :=
  inferInstanceAs (NormedAddCommGroup (LinearMap.ker (sumHistoryDefect h B)))

instance : NormedSpace ℝ (SumC1History h B) :=
  inferInstanceAs (NormedSpace ℝ (LinearMap.ker (sumHistoryDefect h B)))

instance : CompleteSpace (SumC1History h B) :=
  (ContinuousLinearMap.isComplete_ker (sumHistoryDefect h B)).completeSpace_coe

def sumHistoryEquiv : SumC1History h B ≃L[ℝ] C1History h B where
  toLinearEquiv :=
    { toFun := fun x => ⟨WithLp.ofLp x.val, x.property⟩
      invFun := fun x => ⟨WithLp.toLp 1 x.val, x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  continuous_toFun := Continuous.subtype_mk
    ((WithLp.prodContinuousLinearEquiv 1 ℝ (ContinuousHistory h B) (ContinuousHistory h B)).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((WithLp.prodContinuousLinearEquiv 1 ℝ (ContinuousHistory h B) (ContinuousHistory h B)).symm.continuous.comp continuous_subtype_val) _

def sumHistoryInclusion : SumC1History h B →L[ℝ] ContinuousHistory h B :=
  (historyInclusion h B).comp (sumHistoryEquiv h B : SumC1History h B →L[ℝ] C1History h B)

def sumHistoryDerivative : SumC1History h B →L[ℝ] ContinuousHistory h B :=
  (historyDerivative h B).comp (sumHistoryEquiv h B : SumC1History h B →L[ℝ] C1History h B)

def sumEndpointDerivative : SumC1History h B →L[ℝ] B :=
  (endpointDerivative h B).comp (sumHistoryEquiv h B : SumC1History h B →L[ℝ] C1History h B)

theorem sumHistory_norm (x : SumC1History h B) :
    ‖x‖ = ‖sumHistoryInclusion h B x‖ + ‖sumHistoryDerivative h B x‖ :=
  WithLp.prod_norm_eq_of_L1 x.val

theorem sumHistory_norm_comparison (x : SumC1History h B) :
    ‖sumHistoryEquiv h B x‖ ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * ‖sumHistoryEquiv h B x‖ := by
  rw [sumHistory_norm]
  change max ‖x.val.fst‖ ‖x.val.snd‖ ≤ ‖x.val.fst‖ + ‖x.val.snd‖ ∧
    ‖x.val.fst‖ + ‖x.val.snd‖ ≤ 2 * max ‖x.val.fst‖ ‖x.val.snd‖
  constructor
  · exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  · linarith [le_max_left ‖x.val.fst‖ ‖x.val.snd‖, le_max_right ‖x.val.fst‖ ‖x.val.snd‖]

end

end GlobalRegularization
