import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-!
# Actual continuously differentiable histories on a compact interval

A history is a pair `(value, derivative)` of continuous functions satisfying
the fundamental theorem of calculus. The condition is the kernel of a
continuous linear map. Consequently its induced maximum norm is complete.
The theorem `hasDerivWithinAt_value` connects the stored derivative to the
derivative of the value function, including at the boundary.
-/

namespace GlobalRegularization

open Set MeasureTheory
open scoped NNReal

noncomputable section

def HistoryInterval (h : ℝ≥0) := Set.Icc (-(h : ℝ)) 0

instance (h : ℝ≥0) : TopologicalSpace (HistoryInterval h) :=
  inferInstanceAs (TopologicalSpace (Set.Icc (-(h : ℝ)) 0))

instance (h : ℝ≥0) : CompactSpace (HistoryInterval h) :=
  inferInstanceAs (CompactSpace (Set.Icc (-(h : ℝ)) 0))

def historyLeft (h : ℝ≥0) : HistoryInterval h :=
  ⟨-(h : ℝ), le_rfl, neg_nonpos.mpr h.coe_nonneg⟩

def historyRight (h : ℝ≥0) : HistoryInterval h :=
  ⟨0, neg_nonpos.mpr h.coe_nonneg, le_rfl⟩

instance (h : ℝ≥0) : Nonempty (HistoryInterval h) := ⟨historyLeft h⟩

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B]
  [NormedSpace ℝ B] [CompleteSpace B]

abbrev ContinuousHistory := C(HistoryInterval h, B)

/-- Constant continuation of a derivative outside the history interval. -/
def extendHistory (g : ContinuousHistory h B) : ℝ → B :=
  fun t => g (Set.projIcc (-(h : ℝ)) 0 (neg_nonpos.mpr h.coe_nonneg) t)

omit [NormedSpace ℝ B] [CompleteSpace B] in
theorem continuous_extendHistory (g : ContinuousHistory h B) :
    Continuous (extendHistory h B g) :=
  g.continuous.comp continuous_projIcc

omit [NormedSpace ℝ B] [CompleteSpace B] in
theorem uniformContinuous_extendHistory (g : ContinuousHistory h B) :
    UniformContinuous (extendHistory h B g) := by
  have hp := ((LipschitzWith.id.const_min (0 : ℝ)).const_max (-(h : ℝ))).uniformContinuous
  have hproj : UniformContinuous
      (Set.projIcc (-(h : ℝ)) 0 (neg_nonpos.mpr h.coe_nonneg)) := hp.subtype_mk _
  exact (CompactSpace.uniformContinuous_of_continuous g.continuous).comp hproj

omit [NormedSpace ℝ B] [CompleteSpace B] in
@[simp]
theorem extendHistory_coe (g : ContinuousHistory h B) (t : HistoryInterval h) :
    extendHistory h B g t = g t := by
  simp [extendHistory, Set.projIcc_of_mem]

def historyPrimitive (g : ContinuousHistory h B) : ContinuousHistory h B :=
  ⟨fun t => ∫ s in -(h : ℝ)..(t : ℝ), extendHistory h B g s,
    (intervalIntegral.differentiable_integral_of_continuous
      (continuous_extendHistory h B g)).continuous.comp continuous_subtype_val⟩

@[simp]
theorem historyPrimitive_left (g : ContinuousHistory h B) :
    historyPrimitive h B g (historyLeft h) = 0 := by
  simp [historyPrimitive, historyLeft]

theorem norm_historyPrimitive_le (g : ContinuousHistory h B) :
    ‖historyPrimitive h B g‖ ≤ (h : ℝ) * ‖g‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg h.coe_nonneg (norm_nonneg g))).2
  intro t
  have hi : ‖historyPrimitive h B g t‖ ≤ ‖g‖ * |(t : ℝ) - -(h : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => g.norm_coe_le_norm _)
  have ht : |(t : ℝ) - -(h : ℝ)| ≤ (h : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)]
    linarith [t.property.2]
  calc
    ‖historyPrimitive h B g t‖ ≤ ‖g‖ * |(t : ℝ) - -(h : ℝ)| := hi
    _ ≤ ‖g‖ * (h : ℝ) := mul_le_mul_of_nonneg_left ht (norm_nonneg g)
    _ = (h : ℝ) * ‖g‖ := mul_comm _ _

def historyPrimitiveL : ContinuousHistory h B →ₗ[ℝ] ContinuousHistory h B where
  toFun := historyPrimitive h B
  map_add' g k := by
    ext t
    exact intervalIntegral.integral_add (μ := volume)
      ((continuous_extendHistory h B g).intervalIntegrable _ _)
      ((continuous_extendHistory h B k).intervalIntegrable _ _)
  map_smul' c g := by
    ext t
    exact intervalIntegral.integral_smul (μ := volume) c (extendHistory h B g)

def historyPrimitiveCLM : ContinuousHistory h B →L[ℝ] ContinuousHistory h B :=
  (historyPrimitiveL h B).mkContinuous (h : ℝ) (norm_historyPrimitive_le h B)

/-- The reconstruction defect; its kernel is the `C¹` history space. -/
def historyDefect :
    (ContinuousHistory h B × ContinuousHistory h B) →L[ℝ] ContinuousHistory h B :=
  ContinuousLinearMap.fst ℝ _ _ -
    (ContinuousLinearMap.const (R := ℝ) (HistoryInterval h)).comp
      ((ContinuousMap.evalCLM ℝ (historyLeft h)).comp
        (ContinuousLinearMap.fst ℝ _ _)) -
    (historyPrimitiveCLM h B).comp (ContinuousLinearMap.snd ℝ _ _)

def C1History := ↥(LinearMap.ker (historyDefect h B))

instance : NormedAddCommGroup (C1History h B) :=
  inferInstanceAs (NormedAddCommGroup (LinearMap.ker (historyDefect h B)))

instance : NormedSpace ℝ (C1History h B) :=
  inferInstanceAs (NormedSpace ℝ (LinearMap.ker (historyDefect h B)))

instance : CompleteSpace (C1History h B) :=
  (ContinuousLinearMap.isComplete_ker (historyDefect h B)).completeSpace_coe

def historyInclusion : C1History h B →L[ℝ] ContinuousHistory h B :=
  (ContinuousLinearMap.fst ℝ _ _).comp (LinearMap.ker (historyDefect h B)).subtypeL

def historyDerivative : C1History h B →L[ℝ] ContinuousHistory h B :=
  (ContinuousLinearMap.snd ℝ _ _).comp (LinearMap.ker (historyDefect h B)).subtypeL

def historyDerivativeAt (t : HistoryInterval h) : C1History h B →L[ℝ] B :=
  (ContinuousMap.evalCLM ℝ t).comp (historyDerivative h B)

def endpointDerivative : C1History h B →L[ℝ] B :=
  historyDerivativeAt h B (historyRight h)

theorem history_integral_identity (x : C1History h B) (t : HistoryInterval h) :
    historyInclusion h B x t = historyInclusion h B x (historyLeft h) +
      ∫ s in -(h : ℝ)..(t : ℝ), extendHistory h B (historyDerivative h B x) s := by
  have hx := congrArg (fun g : ContinuousHistory h B => g t) x.property
  change x.val.1 t - x.val.1 (historyLeft h) - historyPrimitive h B x.val.2 t = 0 at hx
  change x.val.1 t = x.val.1 (historyLeft h) + historyPrimitive h B x.val.2 t
  exact sub_eq_zero.mp (by simpa [sub_add_eq_sub_sub] using hx)

/-- The primitive gives a genuine differentiable extension of every history. -/
def differentiableHistoryExtension (x : C1History h B) : ℝ → B :=
  fun t => historyInclusion h B x (historyLeft h) +
    ∫ s in -(h : ℝ)..t, extendHistory h B (historyDerivative h B x) s

theorem hasDerivAt_historyExtension_all (x : C1History h B) (t : ℝ) :
    HasDerivAt (differentiableHistoryExtension h B x)
      (extendHistory h B (historyDerivative h B x) t) t := by
  have hc := continuous_extendHistory h B (historyDerivative h B x)
  exact (intervalIntegral.integral_hasDerivAt_right
    (a := -(h : ℝ)) (b := t) (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (historyInclusion h B x (historyLeft h))

theorem differentiableHistoryExtension_add (x y : C1History h B) (t : ℝ) :
    differentiableHistoryExtension h B (x + y) t =
      differentiableHistoryExtension h B x t + differentiableHistoryExtension h B y t := by
  have hInt : (∫ s in -(h : ℝ)..t, extendHistory h B (historyDerivative h B (x + y)) s) =
      (∫ s in -(h : ℝ)..t, extendHistory h B (historyDerivative h B x) s) +
      ∫ s in -(h : ℝ)..t, extendHistory h B (historyDerivative h B y) s := by
    simpa only [map_add, extendHistory, ContinuousMap.add_apply] using
      intervalIntegral.integral_add
        ((continuous_extendHistory h B (historyDerivative h B x)).intervalIntegrable (-(h : ℝ)) t)
        ((continuous_extendHistory h B (historyDerivative h B y)).intervalIntegrable (-(h : ℝ)) t)
  unfold differentiableHistoryExtension
  rw [hInt]
  simp only [map_add, ContinuousMap.add_apply]
  abel

theorem differentiableHistoryExtension_smul (c : ℝ) (x : C1History h B) (t : ℝ) :
    differentiableHistoryExtension h B (c • x) t = c • differentiableHistoryExtension h B x t := by
  have hInt : (∫ s in -(h : ℝ)..t, extendHistory h B (historyDerivative h B (c • x)) s) =
      c • ∫ s in -(h : ℝ)..t, extendHistory h B (historyDerivative h B x) s := by
    simpa only [map_smul, extendHistory, ContinuousMap.smul_apply] using
      intervalIntegral.integral_smul (μ := volume) c (extendHistory h B (historyDerivative h B x))
        (a := -(h : ℝ)) (b := t)
  unfold differentiableHistoryExtension
  rw [hInt]
  simp only [map_smul, ContinuousMap.smul_apply, smul_add]

theorem differentiableHistoryExtension_coe (x : C1History h B)
    (t : HistoryInterval h) :
    differentiableHistoryExtension h B x t = historyInclusion h B x t :=
  (history_integral_identity h B x t).symm

theorem hasDerivAt_historyExtension (x : C1History h B) (t : HistoryInterval h) :
    HasDerivAt (differentiableHistoryExtension h B x)
      (historyDerivative h B x t) t := by
  have hc := continuous_extendHistory h B (historyDerivative h B x)
  have hi := intervalIntegral.integral_hasDerivAt_right
    (a := -(h : ℝ)) (b := (t : ℝ)) (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hh := hi.const_add (historyInclusion h B x (historyLeft h))
  rw [extendHistory_coe] at hh
  exact hh

theorem hasDerivWithinAt_value (x : C1History h B) (t : HistoryInterval h) :
    HasDerivWithinAt (extendHistory h B (historyInclusion h B x))
      (historyDerivative h B x t) (Set.Icc (-(h : ℝ)) 0) t := by
  apply (hasDerivAt_historyExtension h B x t).hasDerivWithinAt.congr_of_mem
  · intro s hs
    change extendHistory h B (historyInclusion h B x) (⟨s, hs⟩ : HistoryInterval h) = _
    rw [extendHistory_coe]
    exact (differentiableHistoryExtension_coe h B x ⟨s, hs⟩).symm
  · exact t.property

theorem historyInclusion_injective (hh : 0 < (h : ℝ)) :
    Function.Injective (historyInclusion h B) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · apply ContinuousMap.ext
    intro t
    have hx := hasDerivWithinAt_value h B x t
    have hy := hasDerivWithinAt_value h B y t
    rw [hxy] at hx
    exact (uniqueDiffOn_Icc (neg_lt_zero.mpr hh) t t.property).eq_deriv _ hx hy

/-- Every endpoint value and continuous derivative reconstruct a history. -/
def historyReconstruct (a : B) (g : ContinuousHistory h B) : C1History h B :=
  ⟨(ContinuousMap.const (HistoryInterval h) a + historyPrimitive h B g, g), by
    ext t
    simp [historyDefect, historyPrimitiveCLM, historyPrimitiveL]⟩

@[simp]
theorem historyReconstruct_derivative (a : B) (g : ContinuousHistory h B) :
    historyDerivative h B (historyReconstruct h B a g) = g := rfl

@[simp]
theorem historyReconstruct_left (a : B) (g : ContinuousHistory h B) :
    historyInclusion h B (historyReconstruct h B a g) (historyLeft h) = a := by
  change a + historyPrimitive h B g (historyLeft h) = a
  simp

theorem historyReconstruct_coordinates (x : C1History h B) :
    historyReconstruct h B (historyInclusion h B x (historyLeft h))
      (historyDerivative h B x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    exact (history_integral_identity h B x t).symm
  · rfl

def historyCoordinates : C1History h B ≃L[ℝ] B × ContinuousHistory h B :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := fun x => (historyInclusion h B x (historyLeft h), historyDerivative h B x)
      invFun := fun p => historyReconstruct h B p.1 p.2
      left_inv := historyReconstruct_coordinates h B
      right_inv := by intro p; ext <;> simp
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }
    1 (1 + (h : ℝ))
    (by
      intro x
      change max ‖x.val.1 (historyLeft h)‖ ‖x.val.2‖ ≤ 1 * ‖x.val‖
      simp only [one_mul, Prod.norm_def]
      exact max_le_max (x.val.1.norm_coe_le_norm _) le_rfl)
    (by
      intro p
      change max ‖ContinuousMap.const (HistoryInterval h) p.1 +
        historyPrimitive h B p.2‖ ‖p.2‖ ≤ (1 + (h : ℝ)) * max ‖p.1‖ ‖p.2‖
      apply max_le
      · calc
          _ ≤ ‖p.1‖ + (h : ℝ) * ‖p.2‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add ((ContinuousMap.norm_le _ (norm_nonneg p.1)).2
                (fun _ => le_rfl)) (norm_historyPrimitive_le h B _))
          _ ≤ _ := by
            have h1 := le_max_left ‖p.1‖ ‖p.2‖
            have h2 := mul_le_mul_of_nonneg_left (le_max_right ‖p.1‖ ‖p.2‖) h.coe_nonneg
            nlinarith
      · have hp := le_max_right ‖p.1‖ ‖p.2‖
        have hm : 0 ≤ (h : ℝ) * max ‖p.1‖ ‖p.2‖ :=
          mul_nonneg h.coe_nonneg (le_trans (norm_nonneg _) hp)
        nlinarith)

/-- Conversely, a continuous function with a continuous derivative on the
closed interval belongs to the integral model. -/
def historyOfClassical (u g : ContinuousHistory h B)
    (hg : ∀ t : HistoryInterval h,
      HasDerivWithinAt (extendHistory h B u) (g t)
        (Set.Icc (-(h : ℝ)) 0) t) : C1History h B :=
  ⟨(u, g), by
    ext t
    have hc := continuous_extendHistory h B u
    have hd := continuous_extendHistory h B g
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := -(h : ℝ)) (b := (t : ℝ)) t.property.1 hc.continuousOn
      (f' := extendHistory h B g)
      (fun s hs => by
        have hsi : s ∈ Set.Icc (-(h : ℝ)) 0 :=
          ⟨hs.1.le, hs.2.le.trans t.property.2⟩
        have hsi' : Set.Icc (-(h : ℝ)) 0 ∈ nhds s :=
          Icc_mem_nhds hs.1 (hs.2.trans_le t.property.2)
        have hf := (hg ⟨s, hsi⟩).hasDerivAt hsi'
        simpa only [← extendHistory_coe h B g ⟨s, hsi⟩] using hf)
      (hd.intervalIntegrable _ _)
    rw [extendHistory_coe h B u t] at hFTC
    have hleft : extendHistory h B u (-(h : ℝ)) = u (historyLeft h) :=
      extendHistory_coe h B u (historyLeft h)
    rw [hleft] at hFTC
    change u t - u (historyLeft h) - historyPrimitive h B g t = 0
    exact sub_eq_zero.mpr hFTC.symm⟩

@[simp]
theorem historyOfClassical_value (u g : ContinuousHistory h B)
    (hg : ∀ t : HistoryInterval h,
      HasDerivWithinAt (extendHistory h B u) (g t)
        (Set.Icc (-(h : ℝ)) 0) t) :
    historyInclusion h B (historyOfClassical h B u g hg) = u := rfl

/-- Restrict a globally `C¹` function to the history interval. -/
def historyOfC1Function (u g : ℝ → B) (hc : Continuous u) (hg : Continuous g)
    (hu : ∀ t, HasDerivAt u (g t) t) : C1History h B :=
  historyOfClassical h B
    ⟨fun t => u t, hc.comp continuous_subtype_val⟩
    ⟨fun t => g t, hg.comp continuous_subtype_val⟩
    (fun t => (hu t).hasDerivWithinAt.congr_of_mem
      (fun s hs => by
        exact extendHistory_coe h B
          ⟨fun t => u t, hc.comp continuous_subtype_val⟩ ⟨s, hs⟩)
      t.property)

@[simp]
theorem historyOfC1Function_value (u g : ℝ → B) (hc : Continuous u) (hg : Continuous g)
    (hu : ∀ t, HasDerivAt u (g t) t) (t : HistoryInterval h) :
    historyInclusion h B (historyOfC1Function h B u g hc hg hu) t = u t := rfl

@[simp]
theorem historyOfC1Function_derivative (u g : ℝ → B) (hc : Continuous u) (hg : Continuous g)
    (hu : ∀ t, HasDerivAt u (g t) t) (t : HistoryInterval h) :
    historyDerivative h B (historyOfC1Function h B u g hc hg hu) t = g t := rfl

end

end GlobalRegularization
