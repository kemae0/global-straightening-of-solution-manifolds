import GlobalRegularization.ChartSubmersion
import GlobalRegularization.BoundaryLayer
import GlobalRegularization.RealComplexification
import Mathlib.Analysis.Normed.Operator.Banach

/-! The revised manuscript's endpoint reflection is an involution.
Its defect identity is valid, but it cannot have derivative spectrum {1}. -/

namespace GlobalRegularization

open Set
open scoped NNReal

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def endpointReflection (D : E →L[ℝ] B) (Q : B →L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (2 : ℝ) • Q.comp D

theorem endpointReflection_endpoint (D : E →L[ℝ] B) (Q : B →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ B) (x : E) : D (endpointReflection D Q x) = -D x := by
  have hqa : D (Q (D x)) = D x := congrArg (fun L : B →L[ℝ] B => L (D x)) hQ
  change D (x - (2 : ℝ) • Q (D x)) = -D x
  rw [map_sub, map_smul, hqa]
  module

theorem endpointReflection_involution (D : E →L[ℝ] B) (Q : B →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ B) : Function.Involutive (endpointReflection D Q) := by
  intro x
  change endpointReflection D Q x - (2 : ℝ) • Q (D (endpointReflection D Q x)) = x
  rw [endpointReflection_endpoint D Q hQ, map_neg]
  change (x - (2 : ℝ) • Q (D x)) - (2 : ℝ) • -Q (D x) = x
  module

def endpointReflectionEquiv (D : E →L[ℝ] B) (Q : B →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ B) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toLinearMap := (endpointReflection D Q).toLinearMap
      invFun := endpointReflection D Q
      left_inv := endpointReflection_involution D Q hQ
      right_inv := endpointReflection_involution D Q hQ }
  continuous_toFun := (endpointReflection D Q).continuous
  continuous_invFun := (endpointReflection D Q).continuous

theorem neg_one_mem_complexified_spectrum_of_endpoint_flip [Nontrivial B]
    (D : E →L[ℝ] B) (Q : B →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ B)
    (M : E →L[ℝ] E) (hM : ∀ y, D (M y) = -D y) :
    (-1 : ℂ) ∈ spectrum ℂ (RealComplexification.map M) := by
  have hnon : ¬ IsUnit (1 + RealComplexification.map M) := by
    intro hu
    obtain ⟨a, ha⟩ := exists_ne (0 : B)
    obtain ⟨v, hv⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2 (RealComplexification.embed (Q a))
    have hd : (RealComplexification.map D) ((1 + RealComplexification.map M) v) = 0 := by
      apply RealComplexification.ext
      intro z
      change D (v z + M (v z)) = 0
      rw [map_add, hM, add_neg_cancel]
    rw [hv, RealComplexification.map_embed] at hd
    have hzero := congrArg (fun w : RealComplexification B => w 1) hd
    have hqa : D (Q a) = a := congrArg (fun L : B →L[ℝ] B => L a) hQ
    simp only [RealComplexification.embed_apply, Complex.one_re, one_smul, RealComplexification.zero_apply, hqa] at hzero
    exact ha hzero
  rw [spectrum.mem_iff]
  intro hu
  apply hnon
  have hscalar : algebraMap ℂ (RealComplexification E →L[ℂ] RealComplexification E) (-1) = -1 := by simp
  rw [hscalar] at hu
  convert hu.neg using 1 <;> noncomm_ring

theorem C1Straightening.twice_endpoint_spectrum_obstruction [Nontrivial B]
    {U : Set E} (hU : IsOpen U) (D : E →L[ℝ] B) (Q : B →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ B)
    (chart : C1Straightening U D (fun x => (2 : ℝ) • D x)) {x : E} (hx : x ∈ U) :
    spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) ≠ {1} := by
  have hd := chart.defect_derivative hU hx
  have heq : (fun y => D y - (2 : ℝ) • D y) = fun y => -D y := by funext y; module
  rw [heq] at hd
  have hder : fderiv ℝ (fun y => -D y) x = -D := D.hasFDerivAt.neg.fderiv
  rw [hder] at hd
  have hm (y : E) : D (fderiv ℝ chart.forward x y) = -D y :=
    (congrArg (fun L : E →L[ℝ] B => L y) hd).symm
  intro hs
  have hn := neg_one_mem_complexified_spectrum_of_endpoint_flip D Q hQ (fderiv ℝ chart.forward x) hm
  rw [hs, mem_singleton_iff] at hn
  norm_num at hn

end

end GlobalRegularization
