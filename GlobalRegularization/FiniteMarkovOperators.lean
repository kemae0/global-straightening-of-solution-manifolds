import GlobalRegularization.WeightedAverages
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Positive finite-rank averaging operators constructed from a finite
continuous partition of unity and a finite measure. -/

namespace GlobalRegularization

open Set MeasureTheory

noncomputable section

variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [Fintype ι]
  (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B]

def partitionSynthesisL (ψ : ι → C(X, ℝ)) : (ι → B) →ₗ[ℝ] C(X, B) where
  toFun c := ∑ j, ψ j • ContinuousMap.const X (c j)
  map_add' c d := by ext x; simp [smul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    ext x
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact smul_comm _ _ _

theorem norm_partitionSynthesis_le (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1) (c : ι → B) :
    ‖partitionSynthesisL B ψ c‖ ≤ ‖c‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg c)).2
  intro x
  change ‖(∑ j, ψ j • ContinuousMap.const X (c j)) x‖ ≤ _
  rw [ContinuousMap.sum_apply]
  calc
    _ ≤ ∑ j, ‖ψ j x • c j‖ := norm_sum_le _ _
    _ = ∑ j, ψ j x * ‖c j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ j x)]
    _ ≤ ∑ j, ψ j x * ‖c‖ := Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm c j) (hψ j x))
    _ = ‖c‖ := by rw [← Finset.sum_mul, hsum, one_mul]

def partitionSynthesis (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1) : (ι → B) →L[ℝ] C(X, B) :=
  (partitionSynthesisL B ψ).mkContinuous 1 (fun c => by
    simpa only [one_mul] using norm_partitionSynthesis_le B ψ hψ hsum c)

variable [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] [CompleteSpace B]

def partitionAverages (ψ : ι → C(X, ℝ)) (hψ : ∀ j x, 0 ≤ ψ j x) : C(X, B) →L[ℝ] (ι → B) :=
  ContinuousLinearMap.pi (fun j => weightedAverage μ B (ψ j) (hψ j))

def finiteMarkovOperator (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1) : C(X, B) →L[ℝ] C(X, B) :=
  (partitionSynthesis B ψ hψ hsum).comp (partitionAverages B μ ψ hψ)

omit [CompleteSpace B] in
theorem finiteMarkovOperator_apply (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1) (g : C(X, B)) (t : X) :
    finiteMarkovOperator B μ ψ hψ hsum g t = ∑ j, ψ j t •
      ((∫ s, ψ j s ∂μ)⁻¹ • ∫ s, ψ j s • g s ∂μ) := by
  simp [finiteMarkovOperator, partitionSynthesis, partitionSynthesisL, partitionAverages,
    weightedAverage, weightedAverageL]

omit [CompleteSpace B] in
theorem norm_finiteMarkovOperator_apply_le (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1) (g : C(X, B)) :
    ‖finiteMarkovOperator B μ ψ hψ hsum g‖ ≤ ‖g‖ := by
  calc
    _ ≤ ‖partitionAverages B μ ψ hψ g‖ := norm_partitionSynthesis_le B ψ hψ hsum _
    _ ≤ ‖g‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg g)).mpr (fun j =>
      norm_weightedAverage_le μ B (ψ j) (hψ j) g)

omit [CompleteSpace B] in
theorem norm_finiteMarkovOperator_le (ψ : ι → C(X, ℝ))
    (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1) :
    ‖finiteMarkovOperator B μ ψ hψ hsum‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun g => by
    simpa only [one_mul] using norm_finiteMarkovOperator_apply_le B μ ψ hψ hsum g)

omit [CompleteSpace B] in
theorem finiteMarkovOperator_finite_range [FiniteDimensional ℝ B]
    (ψ : ι → C(X, ℝ)) (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1) :
    FiniteDimensional ℝ (LinearMap.range (finiteMarkovOperator B μ ψ hψ hsum)) := by
  have hr : LinearMap.range (finiteMarkovOperator B μ ψ hψ hsum) ≤
      LinearMap.range (partitionSynthesis B ψ hψ hsum) := by
    rintro y ⟨g, rfl⟩
    exact ⟨partitionAverages B μ ψ hψ g, rfl⟩
  letI : FiniteDimensional ℝ (LinearMap.range (partitionSynthesis B ψ hψ hsum)) :=
    inferInstanceAs (FiniteDimensional ℝ (LinearMap.range (partitionSynthesis B ψ hψ hsum).toLinearMap))
  exact FiniteDimensional.of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)

end

end GlobalRegularization
