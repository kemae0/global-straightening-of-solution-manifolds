import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# Bounded positive finite-observation Bernstein operators

The operators act on actual continuous Banach-valued functions on the
unit interval. Their contraction estimate uses positivity and the exact
partition-of-unity identity. Strong convergence is mathlib's Bernstein
theorem. The later `C¹` history-space approximation requires a separate
derivative argument and is not asserted here.
-/

namespace GlobalRegularization

open Filter
open scoped unitInterval Topology

noncomputable section

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B]

def bernsteinSynthesisL (n : ℕ) : (Fin (n + 1) → B) →ₗ[ℝ] C(I, B) where
  toFun c := ∑ k : Fin (n + 1), bernstein n k • ContinuousMap.const I (c k)
  map_add' c d := by
    ext t
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    ext t
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact smul_comm _ _ _

theorem norm_bernsteinSynthesis_le (n : ℕ) (c : Fin (n + 1) → B) :
    ‖bernsteinSynthesisL B n c‖ ≤ ‖c‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg c)).2
  intro t
  have heval : bernsteinSynthesisL B n c t =
      ∑ k : Fin (n + 1), bernstein n k t • c k := by simp [bernsteinSynthesisL]
  rw [heval]
  calc
    _ ≤ ∑ k : Fin (n + 1), ‖bernstein n k t • c k‖ := norm_sum_le _ _
    _ = ∑ k : Fin (n + 1), bernstein n k t * ‖c k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n + 1), bernstein n k t * ‖c‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm c k) bernstein_nonneg
    _ = ‖c‖ := by rw [← Finset.sum_mul, bernstein.probability, one_mul]

def bernsteinSynthesis (n : ℕ) : (Fin (n + 1) → B) →L[ℝ] C(I, B) :=
  (bernsteinSynthesisL B n).mkContinuous 1
    (fun c => by simpa only [one_mul] using norm_bernsteinSynthesis_le B n c)

@[simp]
theorem bernsteinSynthesis_apply (n : ℕ) (c : Fin (n + 1) → B) (t : I) :
    bernsteinSynthesis B n c t = ∑ k : Fin (n + 1), bernstein n k t • c k := by
  simp [bernsteinSynthesis, bernsteinSynthesisL]

def bernsteinSamples (n : ℕ) : C(I, B) →L[ℝ] (Fin (n + 1) → B) :=
  ContinuousLinearMap.pi (fun k => ContinuousMap.evalCLM ℝ (bernstein.z k))

@[simp]
theorem bernsteinSamples_apply (n : ℕ) (f : C(I, B)) (k : Fin (n + 1)) :
    bernsteinSamples B n f k = f (bernstein.z k) := rfl

def bernsteinCLM (n : ℕ) : C(I, B) →L[ℝ] C(I, B) :=
  (bernsteinSynthesis B n).comp (bernsteinSamples B n)

@[simp]
theorem bernsteinCLM_eq (n : ℕ) (f : C(I, B)) :
    bernsteinCLM B n f = bernsteinApproximation n f := rfl

theorem norm_bernsteinCLM_apply_le (n : ℕ) (f : C(I, B)) :
    ‖bernsteinCLM B n f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖bernsteinSamples B n f‖ := norm_bernsteinSynthesis_le B n _
    _ ≤ ‖f‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
      intro k
      exact f.norm_coe_le_norm (bernstein.z k)

theorem norm_bernsteinCLM_le (n : ℕ) : ‖bernsteinCLM B n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa only [one_mul] using norm_bernsteinCLM_apply_le B n f)

theorem bernsteinCLM_strong (f : C(I, B)) :
    Tendsto (fun n => bernsteinCLM B n f) atTop (𝓝 f) :=
  bernsteinApproximation_uniform f

theorem bernsteinCLM_finite_range [FiniteDimensional ℝ B] (n : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (bernsteinCLM B n)) := by
  have hr : LinearMap.range (bernsteinCLM B n) ≤ LinearMap.range (bernsteinSynthesis B n) := by
    rintro y ⟨f, rfl⟩
    exact ⟨bernsteinSamples B n f, rfl⟩
  letI : FiniteDimensional ℝ (LinearMap.range (bernsteinSynthesis B n)) :=
    inferInstanceAs (FiniteDimensional ℝ (LinearMap.range (bernsteinSynthesis B n).toLinearMap))
  exact FiniteDimensional.of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)

/-- Uniformly small perturbations of the nodal coefficients preserve
strong convergence of the Bernstein synthesis. -/
theorem bernsteinSynthesis_moving_coefficients
    (f : C(I, B)) (c : ∀ n : ℕ, Fin (n + 1) → B)
    (hcoeff : Tendsto (fun n => ‖c n - bernsteinSamples B n f‖) atTop (𝓝 0)) :
    Tendsto (fun n => bernsteinSynthesis B n (c n)) atTop (𝓝 f) := by
  have herr : Tendsto (fun n => bernsteinSynthesis B n (c n) - bernsteinCLM B n f)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hcoeff
    intro n
    have hn := norm_bernsteinSynthesis_le B n (c n - bernsteinSamples B n f)
    simpa only [← bernsteinCLM_eq, map_sub, bernsteinCLM, ContinuousLinearMap.comp_apply] using hn
  have ht := herr.add (bernsteinCLM_strong B f)
  simpa only [sub_add_cancel, zero_add] using ht

end

end GlobalRegularization
