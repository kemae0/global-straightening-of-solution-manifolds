import GlobalRegularization.BernsteinOperators

/-! A quantitative Bernstein error estimate for Lipschitz functions.
The bound is uniform over functions with a common Lipschitz constant;
this is stronger than pointwise strong convergence and is needed for
approximation in the continuous-history operator norm. -/

namespace GlobalRegularization

open scoped unitInterval Topology

noncomputable section

theorem abs_le_delta_add_sq_div (r δ : ℝ) (hδ : 0 < δ) :
    |r| ≤ δ + r ^ 2 / δ := by
  have hsq := sq_nonneg (|r| - δ)
  have hprod := mul_nonneg (abs_nonneg r) hδ.le
  calc
    |r| ≤ (δ ^ 2 + r ^ 2) / δ := (le_div_iff₀ hδ).mpr (by nlinarith [sq_abs r])
    _ = δ + r ^ 2 / δ := by field_simp

theorem bernstein_weighted_distance_le (n : ℕ) (hn : 0 < n) (t : I)
    (δ : ℝ) (hδ : 0 < δ) :
    (∑ k : Fin (n + 1), bernstein n k t * |(t : ℝ) - bernstein.z k|) ≤
      δ + 1 / ((n : ℝ) * δ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : (∑ k : Fin (n + 1), bernstein n k t *
      (δ + ((t : ℝ) - bernstein.z k) ^ 2 / δ)) =
      δ * (∑ k : Fin (n + 1), bernstein n k t) +
        (∑ k : Fin (n + 1), ((t : ℝ) - bernstein.z k) ^ 2 * bernstein n k t) / δ := by
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ ≤ ∑ k : Fin (n + 1), bernstein n k t *
        (δ + ((t : ℝ) - bernstein.z k) ^ 2 / δ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (abs_le_delta_add_sq_div _ δ hδ) bernstein_nonneg
    _ = δ + ((t : ℝ) * (1 - t) / n) / δ := by
      rw [hs, bernstein.probability, bernstein.variance hn.ne']
      ring
    _ ≤ δ + 1 / ((n : ℝ) * δ) := by
      have ht0 := t.property.1
      have ht1 := t.property.2
      have hprod : (t : ℝ) * (1 - t) ≤ 1 := by nlinarith [sq_nonneg (t : ℝ)]
      have hd := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hprod hnR.le) hδ.le
      have heq : (1 / (n : ℝ)) / δ = 1 / ((n : ℝ) * δ) := by ring
      rw [heq] at hd
      linarith

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem bernstein_lipschitz_error_le
    (f : C(I, B)) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : I, ‖f s - f t‖ ≤ L * |(s : ℝ) - t|)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    ‖bernsteinCLM B n f - f‖ ≤ L * (δ + 1 / ((n : ℝ) * δ)) := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have heq : (∑ k : Fin (n + 1), bernstein n k t • (f (bernstein.z k) - f t)) =
      bernsteinCLM B n f t - f t := by
    simp [bernsteinCLM_eq, bernsteinApproximation.apply, smul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_smul, bernstein.probability]
  change ‖bernsteinCLM B n f t - f t‖ ≤ _
  rw [← heq]
  calc
    _ ≤ ∑ k : Fin (n + 1), ‖bernstein n k t • (f (bernstein.z k) - f t)‖ := norm_sum_le _ _
    _ = ∑ k : Fin (n + 1), bernstein n k t * ‖f (bernstein.z k) - f t‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n + 1), bernstein n k t * (L * |(t : ℝ) - bernstein.z k|) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ bernstein_nonneg
      simpa only [abs_sub_comm] using hlip (bernstein.z k) t
    _ = L * ∑ k : Fin (n + 1), bernstein n k t * |(t : ℝ) - bernstein.z k| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ L * (δ + 1 / ((n : ℝ) * δ)) :=
      mul_le_mul_of_nonneg_left (bernstein_weighted_distance_le n hn t δ hδ) hL

end

end GlobalRegularization
