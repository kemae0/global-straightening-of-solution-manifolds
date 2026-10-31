import GlobalRegularization.VanishingSeries
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Locally uniform convergence of shell series from the manuscript's
tolerance-dependent neighborhood estimates. No fixed neighborhood for
all tolerances is assumed. -/

namespace GlobalRegularization

open Set Filter Metric
open scoped Topology Uniformity

variable {D V E : Type*} [PseudoMetricSpace D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def LocallyVanishing (U : Set D) (a : ℕ → D → V) : Prop :=
  ∀ x ∈ U, ∀ η > 0, ∃ r > 0, ball x r ⊆ U ∧ ∃ N : ℕ,
    ∀ n ≥ N, ∀ y ∈ ball x r, ‖a n y‖ ≤ η

omit [NormedSpace ℝ V] in
theorem LocallyVanishing.tendsto_zero {U : Set D} {a : ℕ → D → V}
    (ha : LocallyVanishing U a) {x : D} (hx : x ∈ U) :
    Tendsto (fun n => a n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr, hball, N, hN⟩ := ha x hx (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  exact (hN n hn x (mem_ball_self hr)).trans_lt (by linarith)

theorem summable_linear_series_of_locally_vanishing
    (S : ℕ → V →L[ℝ] E) (K : ℝ) (hK : 0 < K) (hbound : HasMaxFiniteSumBound S K)
    {U : Set D} (a : ℕ → D → V) (ha : LocallyVanishing U a) {x : D} (hx : x ∈ U) :
    Summable (fun n => S n (a n x)) :=
  summable_of_vanishing_coefficients S K hK hbound (fun n => a n x) (ha.tendsto_zero hx)

theorem locally_uniform_linear_series_of_locally_vanishing
    (S : ℕ → V →L[ℝ] E) (K : ℝ) (hK : 0 < K) (hbound : HasMaxFiniteSumBound S K)
    {U : Set D} (a : ℕ → D → V) (ha : LocallyVanishing U a) :
    TendstoLocallyUniformlyOn (fun N x => ∑ n ∈ Finset.range N, S n (a n x))
      (fun x => ∑' n, S n (a n x)) atTop U := by
  intro u hu x hx
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  have hη : 0 < ε / (2 * K) := by positivity
  obtain ⟨r, hr, hball, N, hN⟩ := ha x hx (ε / (2 * K)) hη
  refine ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), ?_⟩
  filter_upwards [eventually_ge_atTop N] with m hm
  intro y hy
  apply hsub
  rw [dist_eq_norm]
  have hsum := summable_linear_series_of_locally_vanishing S K hK hbound a ha (hball hy)
  have htail := norm_tsum_sub_partial_le S K hbound (fun n => a n y) hsum m
    (ε / (2 * K)) hη.le (fun n hn => hN n (hm.trans hn) y hy)
  have heq : K * (ε / (2 * K)) = ε / 2 := by field_simp
  rw [heq] at htail
  exact htail.trans_lt (by linarith)

theorem continuousOn_linear_series_of_locally_vanishing
    (S : ℕ → V →L[ℝ] E) (K : ℝ) (hK : 0 < K) (hbound : HasMaxFiniteSumBound S K)
    {U : Set D} (a : ℕ → D → V) (ha : LocallyVanishing U a)
    (hc : ∀ n, ContinuousOn (a n) U) :
    ContinuousOn (fun x => ∑' n, S n (a n x)) U := by
  apply (locally_uniform_linear_series_of_locally_vanishing S K hK hbound a ha).continuousOn
  apply Eventually.of_forall
  intro N
  exact continuousOn_finset_sum _ (fun n hn => (S n).continuous.comp_continuousOn (hc n))

end GlobalRegularization
