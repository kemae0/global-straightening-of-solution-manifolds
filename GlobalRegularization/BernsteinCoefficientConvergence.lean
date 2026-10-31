import GlobalRegularization.BernsteinDerivative
import GlobalRegularization.SlopeEstimate
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform convergence of the finite-difference coefficients to the
derivative samples. This uses uniform continuity of the actual derivative
and a Banach-valued mean-value estimate, not an extra convergence axiom. -/

namespace GlobalRegularization

open Set Filter
open scoped unitInterval Topology

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem bernstein_grid_geometry {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (k : ℝ) / (n + 1 : ℝ) < (k + 1 : ℝ) / (n + 1 : ℝ) ∧
    (k : ℝ) / n ∈ Icc ((k : ℝ) / (n + 1 : ℝ)) ((k + 1 : ℝ) / (n + 1 : ℝ)) ∧
    (k + 1 : ℝ) / (n + 1 : ℝ) - (k : ℝ) / (n + 1 : ℝ) = 1 / (n + 1 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  constructor
  · exact (div_lt_div_iff_of_pos_right hd).2 (by linarith)
  constructor
  · constructor
    · rw [div_le_div_iff₀ hd hnR]
      nlinarith
    · rw [div_le_div_iff₀ hnR hd]
      nlinarith
  · field_simp
    ring

def bernsteinCurveSamples (u : ℝ → B) (n k : ℕ) : B :=
  u ((k : ℝ) / (n + 1 : ℝ))

def restrictToUnitInterval (g : ℝ → B) (hg : Continuous g) : C(I, B) :=
  ⟨fun t => g t, hg.comp continuous_subtype_val⟩

theorem norm_bernsteinDifferenceCoefficients_le
    (u g : ℝ → B) (hu : ∀ t, HasDerivAt u (g t) t)
    {M : ℝ} (hbound : ∀ t, ‖g t‖ ≤ M) (n k : ℕ) :
    ‖bernsteinDifferenceCoefficients n (bernsteinCurveSamples u n) k‖ ≤ M := by
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have hab : (k : ℝ) / (n + 1 : ℝ) < (k + 1 : ℝ) / (n + 1 : ℝ) :=
    (div_lt_div_iff_of_pos_right hd).2 (by linarith)
  have hlen : (k + 1 : ℝ) / (n + 1 : ℝ) - (k : ℝ) / (n + 1 : ℝ) = 1 / (n + 1 : ℝ) := by
    field_simp
    ring
  have hm := (convex_Icc ((k : ℝ) / (n + 1 : ℝ)) ((k + 1 : ℝ) / (n + 1 : ℝ))).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hu t).hasDerivWithinAt) (fun t ht => hbound t)
    (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab), hlen] at hm
  simp only [bernsteinDifferenceCoefficients, bernsteinCurveSamples,
    Nat.cast_add, Nat.cast_one, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
  calc
    _ ≤ (n + 1 : ℝ) * (M * (1 / (n + 1 : ℝ))) := mul_le_mul_of_nonneg_left hm hd.le
    _ = M := by field_simp

theorem bernsteinDifferenceCoefficients_converge
    (u g : ℝ → B) (hu : ∀ t, HasDerivAt u (g t) t) (hg : UniformContinuous g) :
    Tendsto
      (fun n => ‖(fun k : Fin (n + 1) =>
        bernsteinDifferenceCoefficients n (bernsteinCurveSamples u n) k) -
          bernsteinSamples B n (restrictToUnitInterval g hg.continuous)‖)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hg (ε / 2) (by positivity)
  have hwidth : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < δ :=
    (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 δ hδ
  filter_upwards [hwidth, eventually_ge_atTop 1] with n hwidth hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ε / 2)).2
  intro k
  have hkn : (k : ℕ) ≤ n := by omega
  obtain ⟨hab, hz, hlen⟩ := bernstein_grid_geometry (by omega : 0 < n) hkn
  have hbound : ∀ t ∈ Icc ((k : ℝ) / (n + 1 : ℝ)) ((k + 1 : ℝ) / (n + 1 : ℝ)),
      ‖g t - g ((k : ℝ) / n)‖ ≤ ε / 2 := by
    intro t ht
    have hdist : dist t ((k : ℝ) / n) < δ := by
      rw [Real.dist_eq]
      apply lt_of_le_of_lt _ hwidth
      rw [← hlen]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2, hz.1, hz.2]
    exact (by simpa only [dist_eq_norm] using hmod hdist : ‖g t - g ((k : ℝ) / n)‖ < ε / 2).le
  have hs := slope_error_le u g hu hab hbound
  rw [hlen] at hs
  simp only [one_div, inv_inv] at hs
  simpa only [Pi.sub_apply, bernsteinDifferenceCoefficients, bernsteinCurveSamples,
    bernsteinSamples_apply, restrictToUnitInterval, bernstein.z,
    ContinuousMap.coe_mk, Nat.cast_add, Nat.cast_one] using hs

theorem bernstein_derivatives_converge
    (u g : ℝ → B) (hu : ∀ t, HasDerivAt u (g t) t) (hg : UniformContinuous g) :
    Tendsto (fun n => bernsteinCurveCM n
      (bernsteinDifferenceCoefficients n (bernsteinCurveSamples u n)))
      atTop (𝓝 (restrictToUnitInterval g hg.continuous)) :=
  bernsteinCurve_derivatives_tendsto (restrictToUnitInterval g hg.continuous)
    (bernsteinCurveSamples u) (bernsteinDifferenceCoefficients_converge u g hu hg)

end

end GlobalRegularization
