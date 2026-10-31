import GlobalRegularization.FiniteMarkovOperators
import GlobalRegularization.WeightedAverageApproximation
import GlobalRegularization.SmallSupportPartitions

/-! Strong convergence of the constructed positive averaging operators.
The estimates are valid for Banach-valued continuous functions. -/

namespace GlobalRegularization

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section

variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [Fintype ι]
  [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem norm_finiteMarkovOperator_sub_le
    (ψ : ι → C(X, ℝ)) (hψ : ∀ j x, 0 ≤ ψ j x) (hsum : ∀ x, ∑ j, ψ j x = 1)
    (hfull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < μ U)
    (g : C(X, B)) (η : ℝ) (hη : 0 ≤ η)
    (hosc : ∀ j x y, ψ j x ≠ 0 → ψ j y ≠ 0 → ‖g y - g x‖ ≤ η) :
    ‖finiteMarkovOperator B μ ψ hψ hsum g - g‖ ≤ η := by
  apply (ContinuousMap.norm_le _ hη).2
  intro x
  have heq : finiteMarkovOperator B μ ψ hψ hsum g x - g x =
      ∑ j, ψ j x • (weightedAverage μ B (ψ j) (hψ j) g - g x) := by
    rw [finiteMarkovOperator_apply]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    rfl
  change ‖finiteMarkovOperator B μ ψ hψ hsum g x - g x‖ ≤ η
  rw [heq]
  calc
    _ ≤ ∑ j, ‖ψ j x • (weightedAverage μ B (ψ j) (hψ j) g - g x)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ψ j x * η := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hx : ψ j x = 0
      · simp only [hx, zero_smul, norm_zero, zero_mul, le_refl]
      · have hne : ψ j ≠ 0 := fun hz => hx (congrArg (fun f : C(X, ℝ) => f x) hz)
        have hd := integral_weight_pos_of_full_support μ (ψ j) (hψ j) hfull hne
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ j x)]
        exact mul_le_mul_of_nonneg_left
          (weightedAverage_sub_const_le μ B (ψ j) (hψ j) hd g (g x) η
            (fun y hy => hosc j x y hx hy)) (hψ j x)
    _ = η := by rw [← Finset.sum_mul, hsum, one_mul]

variable (X : Type*) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

def markovPartition (n : ℕ) : SmallSupportPartition X (1 / (n + 1 : ℝ)) :=
  smallSupportPartition X _ (by positivity)

def markovApproximation (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) : C(X, B) →L[ℝ] C(X, B) :=
  finiteMarkovOperator B μ (markovPartition X n).weight
    (markovPartition X n).nonneg (markovPartition X n).sum_one

theorem markovApproximation_strong (μ : Measure X) [IsFiniteMeasure μ]
    (hfull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < μ U) (g : C(X, B)) :
    Tendsto (fun n => markovApproximation B X μ n g) atTop (𝓝 g) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨η, hη, hnear⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 2) (by positivity)
  have hwidth : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < η :=
    (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp hwidth
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  apply norm_finiteMarkovOperator_sub_le μ B (markovPartition X n).weight
    (markovPartition X n).nonneg (markovPartition X n).sum_one hfull g (ε / 2) (by positivity)
  intro j x y hx hy
  have hd := ((markovPartition X n).support_close j x y hx hy).trans (hN n hn)
  have ht := hnear (by simpa only [dist_comm] using hd)
  exact (show ‖g y - g x‖ < ε / 2 by simpa only [dist_eq_norm, norm_sub_rev] using ht).le

theorem norm_markovApproximation_le (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    ‖markovApproximation B X μ n‖ ≤ 1 :=
  norm_finiteMarkovOperator_le B μ _ _ _

omit [CompleteSpace B] in
theorem markovApproximation_finite_range [FiniteDimensional ℝ B]
    (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (markovApproximation B X μ n)) :=
  finiteMarkovOperator_finite_range B μ _ _ _

end

end GlobalRegularization
