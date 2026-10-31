import GlobalRegularization.HistorySpace

/-! Actual changes of time scale between continuously differentiable
history spaces. Both the function and its derivative are rescaled. -/

namespace GlobalRegularization

open Set
open scoped NNReal Topology

noncomputable section

variable (h k : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def historyScaleTime (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h)
    (t : HistoryInterval k) : HistoryInterval h :=
  ⟨a * (t : ℝ), by
    have ht := t.property
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 ha, mul_le_mul_of_nonneg_left ht.2 ha]⟩

def historyRescale (a : ℝ) (x : C1History h B) : C1History k B :=
  historyOfC1Function k B
    (fun t => differentiableHistoryExtension h B x (a * t))
    (fun t => a • extendHistory h B (historyDerivative h B x) (a * t))
    ((show Differentiable ℝ (differentiableHistoryExtension h B x) from
      fun t => (hasDerivAt_historyExtension_all h B x t).differentiableAt).continuous.comp
        (continuous_const.mul continuous_id))
    (continuous_const.smul ((continuous_extendHistory h B _).comp (continuous_const.mul continuous_id)))
    (fun t => by
      simpa only [Function.comp_def, mul_one] using
        (hasDerivAt_historyExtension_all h B x (a * t)).scomp t ((hasDerivAt_id t).const_mul a))

theorem historyRescale_value (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h)
    (x : C1History h B) (t : HistoryInterval k) :
    historyInclusion k B (historyRescale h k B a x) t =
      historyInclusion h B x (historyScaleTime h k a ha hak t) :=
  differentiableHistoryExtension_coe h B x (historyScaleTime h k a ha hak t)

theorem historyRescale_derivative (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h)
    (x : C1History h B) (t : HistoryInterval k) :
    historyDerivative k B (historyRescale h k B a x) t =
      a • historyDerivative h B x (historyScaleTime h k a ha hak t) := by
  change a • extendHistory h B (historyDerivative h B x) (a * (t : ℝ)) = _
  exact congrArg (fun z : B => a • z)
    (extendHistory_coe h B (historyDerivative h B x) (historyScaleTime h k a ha hak t))

theorem norm_historyRescale_value_le (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h)
    (x : C1History h B) :
    ‖historyInclusion k B (historyRescale h k B a x)‖ ≤ ‖historyInclusion h B x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  rw [historyRescale_value h k B a ha hak]
  exact (historyInclusion h B x).norm_coe_le_norm _

theorem norm_historyRescale_le (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h)
    (x : C1History h B) : ‖historyRescale h k B a x‖ ≤ max 1 ‖a‖ * ‖x‖ := by
  have hv : ‖historyInclusion h B x‖ ≤ ‖x‖ := le_max_left _ _
  have hd : ‖historyDerivative h B x‖ ≤ ‖x‖ := le_max_right _ _
  apply max_le
  · exact (norm_historyRescale_value_le h k B a ha hak x).trans
      (hv.trans (by nlinarith [norm_nonneg x, le_max_left (1 : ℝ) ‖a‖]))
  · have hdr : ‖historyDerivative k B (historyRescale h k B a x)‖ ≤ ‖a‖ * ‖historyDerivative h B x‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro t
      rw [historyRescale_derivative h k B a ha hak, norm_smul]
      exact mul_le_mul_of_nonneg_left ((historyDerivative h B x).norm_coe_le_norm _) (norm_nonneg a)
    exact hdr.trans ((mul_le_mul_of_nonneg_left hd (norm_nonneg a)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x)))

def historyRescaleL (hk : 0 < (k : ℝ)) (a : ℝ) : C1History h B →ₗ[ℝ] C1History k B where
  toFun := historyRescale h k B a
  map_add' x y := by
    apply historyInclusion_injective k B hk
    ext t
    exact differentiableHistoryExtension_add h B x y (a * (t : ℝ))
  map_smul' c x := by
    apply historyInclusion_injective k B hk
    ext t
    exact differentiableHistoryExtension_smul h B c x (a * (t : ℝ))

def historyRescaleCLM (hk : 0 < (k : ℝ)) (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h) :
    C1History h B →L[ℝ] C1History k B :=
  (historyRescaleL h k B hk a).mkContinuous (max 1 ‖a‖) (norm_historyRescale_le h k B a ha hak)

end

end GlobalRegularization
