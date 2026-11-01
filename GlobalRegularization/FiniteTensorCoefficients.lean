import GlobalRegularization.SignedMeasureDuality
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Basic

/-! Continuous coefficient extraction for a finite independent family of
scalar continuous functions with arbitrary Banach-valued coefficients. -/

namespace GlobalRegularization

open Set MeasureTheory

noncomputable section

variable {X ι : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [Fintype ι] [DecidableEq ι]

theorem finite_continuous_biorthogonal (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v) :
    ∃ q : ι → C(X, ℝ) →L[ℝ] ℝ, ∀ j k, q j (v k) = if k = j then 1 else 0 := by
  classical
  let S := Submodule.span ℝ (range v)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (finite_range v)
  let l (j : ι) : S →ₗ[ℝ] ℝ :=
    { toFun := fun z => hv.repr z j
      map_add' := by intro z w; simp
      map_smul' := by intro a z; simp }
  let L (j : ι) : S →L[ℝ] ℝ := ⟨l j, LinearMap.continuous_of_finiteDimensional (l j)⟩
  have hq (j : ι) := Real.exists_extension_norm_eq S (L j)
  choose q hq hnorm using hq
  refine ⟨q, fun j k => ?_⟩
  let z : S := ⟨v k, Submodule.subset_span (mem_range_self k)⟩
  have heq := hq j z
  change q j (v k) = hv.repr z j at heq
  rw [heq, hv.repr_eq_single k z rfl]
  simp only [Finsupp.single_apply, eq_comm]

def continuousVectorIntegralL (μ : Measure X) [IsFiniteMeasure μ]
    (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] : C(X, B) →ₗ[ℝ] B where
  toFun g := ∫ x, g x ∂μ
  map_add' g f := integral_add (continuous_compact_integrable μ B g) (continuous_compact_integrable μ B f)
  map_smul' a g := integral_smul (μ := μ) a g

def continuousVectorIntegral (μ : Measure X) [IsFiniteMeasure μ]
    (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] : C(X, B) →L[ℝ] B :=
  (continuousVectorIntegralL μ B).mkContinuous (μ.real univ) (fun g => by
    have hb := norm_integral_le_of_norm_le (f := fun x => g x) (integrable_const ‖g‖)
      (ae_of_all μ (fun x => g.norm_coe_le_norm x))
    simpa only [continuousVectorIntegralL, integral_const, smul_eq_mul] using hb)

@[simp]
theorem continuousVectorIntegral_apply (μ : Measure X) [IsFiniteMeasure μ]
    (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (g : C(X, B)) :
    continuousVectorIntegral μ B g = ∫ x, g x ∂μ := rfl

theorem finite_tensor_coefficients
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] :
    ∃ q : C(X, B) →L[ℝ] (ι → B),
      ∀ c : ι → B, q (∑ j, v j • ContinuousMap.const X (c j)) = c := by
  classical
  obtain ⟨p, hp⟩ := finite_continuous_biorthogonal v hv
  have hrep (j : ι) := continuousFunctional_riesz_difference (p j)
  choose μ ν hμ hν hrep using hrep
  letI := hμ
  letI := hν
  let Q (j : ι) := continuousVectorIntegral (μ j) B - continuousVectorIntegral (ν j) B
  have hQ (j k : ι) (b : B) : Q j (v k • ContinuousMap.const X b) = (p j (v k)) • b := by
    change (∫ x, v k x • b ∂μ j) - (∫ x, v k x • b ∂ν j) = _
    rw [integral_smul_const, integral_smul_const, ← sub_smul, ← hrep j]
  refine ⟨ContinuousLinearMap.pi Q, fun c => ?_⟩
  ext j
  simp only [ContinuousLinearMap.pi_apply, map_sum, hQ, hp]
  simp

end

end GlobalRegularization
