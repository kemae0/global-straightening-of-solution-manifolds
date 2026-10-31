import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! Unconditional summability from a finite-sum maximum estimate and
vanishing coefficients, including the exact norm bound for every tail. -/

namespace GlobalRegularization

open Filter
open scoped Topology

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasMaxFiniteSumBound (S : ℕ → V →L[ℝ] E) (K : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (a : ℕ → V) (M : ℝ), 0 ≤ M →
    (∀ i ∈ s, ‖a i‖ ≤ M) → ‖∑ i ∈ s, S i (a i)‖ ≤ K * M

theorem summable_of_vanishing_coefficients [CompleteSpace E]
    (S : ℕ → V →L[ℝ] E) (K : ℝ) (hK : 0 < K) (hbound : HasMaxFiniteSumBound S K)
    (a : ℕ → V) (ha : Tendsto a atTop (𝓝 0)) : Summable (fun n => S n (a n)) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hM : 0 < ε / (2 * K) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha (ε / (2 * K)) hM
  refine ⟨Finset.range N, ?_⟩
  intro t ht
  have hcoeff : ∀ i ∈ t, ‖a i‖ ≤ ε / (2 * K) := by
    intro i hi
    have hiN : N ≤ i := by
      by_contra hiN
      exact Finset.disjoint_left.mp ht hi (Finset.mem_range.mpr (by omega))
    exact (by simpa only [dist_zero_right] using hN i hiN : ‖a i‖ < ε / (2 * K)).le
  have h := hbound t a (ε / (2 * K)) hM.le hcoeff
  have heq : K * (ε / (2 * K)) = ε / 2 := by field_simp
  rw [heq] at h
  exact h.trans_lt (by linarith)

theorem norm_tsum_sub_partial_le
    (S : ℕ → V →L[ℝ] E) (K : ℝ) (hbound : HasMaxFiniteSumBound S K)
    (a : ℕ → V) (hsum : Summable (fun n => S n (a n)))
    (N : ℕ) (M : ℝ) (hM : 0 ≤ M) (hcoeff : ∀ n ≥ N, ‖a n‖ ≤ M) :
    ‖(∑' n, S n (a n)) - ∑ n ∈ Finset.range N, S n (a n)‖ ≤ K * M := by
  have ht : Tendsto (fun m => ‖(∑ n ∈ Finset.range m, S n (a n)) -
      ∑ n ∈ Finset.range N, S n (a n)‖) atTop
      (𝓝 ‖(∑' n, S n (a n)) - ∑ n ∈ Finset.range N, S n (a n)‖) :=
    (hsum.hasSum.tendsto_sum_nat.sub tendsto_const_nhds).norm
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop N] with m hm
  rw [← Finset.sum_Ico_eq_sub _ hm]
  exact hbound (Finset.Ico N m) a M hM (fun i hi => hcoeff i (Finset.mem_Ico.mp hi).1)

end GlobalRegularization
