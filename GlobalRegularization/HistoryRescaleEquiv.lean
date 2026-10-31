import GlobalRegularization.HistoryRescale

/-! Bounded linear equivalences for changes of time scale, with the
corresponding continuous-history operator and endpoint identities. -/

namespace GlobalRegularization

open Set
open scoped NNReal Topology

noncomputable section

variable (h k : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem historyRescale_inverse_compatible
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) : a⁻¹ * (h : ℝ) = k := by
  rw [← hak, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

def historyRescaleEquiv (hh : 0 < (h : ℝ)) (hk : 0 < (k : ℝ))
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) : C1History h B ≃L[ℝ] C1History k B where
  toLinearEquiv :=
    { toLinearMap := historyRescaleL h k B hk a
      invFun := historyRescale k h B a⁻¹
      left_inv := by
        intro x
        apply historyInclusion_injective h B hh
        ext t
        change historyInclusion h B (historyRescale k h B a⁻¹ (historyRescale h k B a x)) t =
          historyInclusion h B x t
        rw [historyRescale_value k h B a⁻¹ (inv_nonneg.mpr ha.le)
          (historyRescale_inverse_compatible h k a ha hak), historyRescale_value h k B a ha.le hak]
        apply congrArg (historyInclusion h B x)
        apply Subtype.ext
        change a * (a⁻¹ * (t : ℝ)) = (t : ℝ)
        rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      right_inv := by
        intro x
        apply historyInclusion_injective k B hk
        ext t
        change historyInclusion k B (historyRescale h k B a (historyRescale k h B a⁻¹ x)) t =
          historyInclusion k B x t
        rw [historyRescale_value h k B a ha.le hak, historyRescale_value k h B a⁻¹ (inv_nonneg.mpr ha.le)
          (historyRescale_inverse_compatible h k a ha hak)]
        apply congrArg (historyInclusion k B x)
        apply Subtype.ext
        change a⁻¹ * (a * (t : ℝ)) = (t : ℝ)
        rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] }
  continuous_toFun := (historyRescaleCLM h k B hk a ha.le hak).continuous
  continuous_invFun := (historyRescaleCLM k h B hh a⁻¹ (inv_nonneg.mpr ha.le)
    (historyRescale_inverse_compatible h k a ha hak)).continuous

def continuousHistoryRescaleL (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h) :
    ContinuousHistory h B →ₗ[ℝ] ContinuousHistory k B where
  toFun g := ⟨fun t => g (historyScaleTime h k a ha hak t), by
    apply g.continuous.comp
    exact (continuous_const.mul continuous_subtype_val).subtype_mk _⟩
  map_add' g j := by ext t; rfl
  map_smul' c g := by ext t; rfl

def continuousHistoryRescaleCLM (a : ℝ) (ha : 0 ≤ a) (hak : a * (k : ℝ) = h) :
    ContinuousHistory h B →L[ℝ] ContinuousHistory k B :=
  (continuousHistoryRescaleL h k B a ha hak).mkContinuous 1 (by
    intro g
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg g)).2
    intro t
    exact g.norm_coe_le_norm _)

theorem historyRescale_inclusion_commutes
    (hh : 0 < (h : ℝ)) (hk : 0 < (k : ℝ))
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) :
    (historyInclusion k B).comp
      (historyRescaleEquiv h k B hh hk a ha hak : C1History h B →L[ℝ] C1History k B) =
      (continuousHistoryRescaleCLM h k B a ha.le hak).comp (historyInclusion h B) := by
  apply ContinuousLinearMap.ext
  intro x
  ext t
  exact historyRescale_value h k B a ha.le hak x t

theorem historyRescale_endpoint
    (hh : 0 < (h : ℝ)) (hk : 0 < (k : ℝ))
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) (x : C1History h B) :
    endpointDerivative k B (historyRescaleEquiv h k B hh hk a ha hak x) = a • endpointDerivative h B x := by
  change historyDerivative k B (historyRescale h k B a x) (historyRight k) = _
  rw [historyRescale_derivative h k B a ha.le hak]
  have ht : historyScaleTime h k a ha.le hak (historyRight k) = historyRight h := by
    apply Subtype.ext
    simp only [historyScaleTime, historyRight, mul_zero]
  rw [ht]
  rfl

theorem norm_historyRescaleEquiv_symm_value_le
    (hh : 0 < (h : ℝ)) (hk : 0 < (k : ℝ))
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) (x : C1History k B) :
    ‖historyInclusion h B ((historyRescaleEquiv h k B hh hk a ha hak).symm x)‖ ≤
      ‖historyInclusion k B x‖ :=
  norm_historyRescale_value_le k h B a⁻¹ (inv_nonneg.mpr ha.le)
    (historyRescale_inverse_compatible h k a ha hak) x

theorem historyRescaleEquiv_symm_value
    (hh : 0 < (h : ℝ)) (hk : 0 < (k : ℝ))
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) (x : C1History k B) (t : HistoryInterval h) :
    historyInclusion h B ((historyRescaleEquiv h k B hh hk a ha hak).symm x) t =
      historyInclusion k B x (historyScaleTime k h a⁻¹ (inv_nonneg.mpr ha.le)
        (historyRescale_inverse_compatible h k a ha hak) t) :=
  historyRescale_value k h B a⁻¹ (inv_nonneg.mpr ha.le)
    (historyRescale_inverse_compatible h k a ha hak) x t

theorem historyRescaleEquiv_symm_endpoint
    (hh : 0 < (h : ℝ)) (hk : 0 < (k : ℝ))
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) (x : C1History k B) :
    endpointDerivative h B ((historyRescaleEquiv h k B hh hk a ha hak).symm x) =
      a⁻¹ • endpointDerivative k B x :=
  historyRescale_endpoint k h B hk hh a⁻¹ (inv_pos.mpr ha)
    (historyRescale_inverse_compatible h k a ha hak) x

theorem historyRescaleEquiv_symm_inclusion
    (hh : 0 < (h : ℝ)) (hk : 0 < (k : ℝ))
    (a : ℝ) (ha : 0 < a) (hak : a * (k : ℝ) = h) :
    (historyInclusion h B).comp
      ((historyRescaleEquiv h k B hh hk a ha hak).symm : C1History k B →L[ℝ] C1History h B) =
      (continuousHistoryRescaleCLM k h B a⁻¹ (inv_nonneg.mpr ha.le)
        (historyRescale_inverse_compatible h k a ha hak)).comp (historyInclusion k B) := by
  apply ContinuousLinearMap.ext
  intro x
  ext t
  exact historyRescaleEquiv_symm_value h k B hh hk a ha hak x t

end

end GlobalRegularization
