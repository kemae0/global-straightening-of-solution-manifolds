import GlobalRegularization.HilbertBumps
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Uniform bounds on every derivative of the actual radial Hilbert bumps.
The bounded balls used here need not be compact. -/

namespace GlobalRegularization

open Set Filter Metric Function
open scoped Topology ContDiff

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem affineShift_iterated_bound (c x : H) (r : ℝ) (hx : ‖x - c‖ ≤ r) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : H => y - c) x‖ ≤ max 1 r := by
  rcases k with _ | k
  · simpa only [norm_iteratedFDeriv_zero] using hx.trans (le_max_right 1 r)
  · rw [← norm_iteratedFDeriv_fderiv]
    have hf : fderiv ℝ (fun y : H => y - c) = fun _ => ContinuousLinearMap.id ℝ H := by
      ext y z
      rw [fderiv_sub_const]
      change (fderiv ℝ id y) z = _
      rw [fderiv_id]
    rw [hf]
    rcases k with _ | k
    · rw [norm_iteratedFDeriv_zero]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_left 1 r)
    · simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      exact zero_le_one.trans (le_max_left 1 r)

def hilbertQuadraticDerivativeBound (r : ℝ) (k : ℕ) : ℝ :=
  (r ^ 2)⁻¹ * ‖(innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)‖ *
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * max 1 r * max 1 r

theorem hilbertQuadraticDerivativeBound_nonneg (r : ℝ) (k : ℕ) :
    0 ≤ hilbertQuadraticDerivativeBound (H := H) r k := by
  unfold hilbertQuadraticDerivativeBound
  positivity

theorem hilbertQuadratic_iterated_bound (c x : H) (r : ℝ) (hx : ‖x - c‖ ≤ r) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : H => ‖y - c‖ ^ 2 / r ^ 2) x‖ ≤
      hilbertQuadraticDerivativeBound (H := H) r k := by
  have hb := (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear
    (contDiff_id.sub contDiff_const : ContDiff ℝ ∞ (fun y : H => y - c))
    (contDiff_id.sub contDiff_const : ContDiff ℝ ∞ (fun y : H => y - c)) x (n := k) (mod_cast le_top)
  have heq : (fun y : H => ‖y - c‖ ^ 2 / r ^ 2) =
      (r ^ 2)⁻¹ • (fun y : H => (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) (y - c) (y - c)) := by
    ext y
    change ‖y - c‖ ^ 2 / r ^ 2 = (r ^ 2)⁻¹ * inner ℝ (y - c) (y - c)
    rw [real_inner_self_eq_norm_sq, div_eq_inv_mul]
  rw [heq, iteratedFDeriv_const_smul_apply]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))]
    unfold hilbertQuadraticDerivativeBound
    apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (sq_nonneg r))).trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg r))
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ))
    apply Finset.sum_le_sum
    intro i _
    gcongr
    · exact affineShift_iterated_bound c x r hx i
    · exact affineShift_iterated_bound c x r hx (k - i)
  · exact ((contDiff_id.sub contDiff_const : ContDiff ℝ ∞ (fun y : H => y - c)).inner ℝ
      (contDiff_id.sub contDiff_const)).contDiffAt.of_le (mod_cast le_top)

theorem hilbertBump_all_derivatives_bounded (c : H) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n (hilbertBump c r) x‖ ≤ C := by
  have hs (k : ℕ) : ∃ C : ℝ, ∀ t, ‖iteratedFDeriv ℝ k scalarUnitBump t‖ ≤ C :=
    (scalarUnitBump.hasCompactSupport.iteratedFDeriv k).exists_bound_of_continuous
      (scalarUnitBump.contDiff.continuous_iteratedFDeriv (mod_cast le_top))
  choose C hC using hs
  let A : ℝ := 1 + ∑ k ∈ Finset.range (n + 1), max 0 (C k)
  let D : ℝ := 1 + ∑ k ∈ Finset.range (n + 1), hilbertQuadraticDerivativeBound (H := H) r k
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hD : 1 ≤ D := by
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg (fun k _ => hilbertQuadraticDerivativeBound_nonneg r k)
  have hCbound (k : ℕ) (hk : k ≤ n) (t : ℝ) : ‖iteratedFDeriv ℝ k scalarUnitBump t‖ ≤ A := by
    have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (n + 1)) => le_max_left 0 (C j)) hmem
    exact (hC k t).trans ((le_max_right _ _).trans (hsum.trans (le_add_of_nonneg_left zero_le_one)))
  refine ⟨(n.factorial : ℝ) * A * D ^ n, by positivity, ?_⟩
  intro x
  by_cases hx : ‖x - c‖ ≤ r
  · have hDbound (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
        ‖iteratedFDeriv ℝ k (fun y : H => ‖y - c‖ ^ 2 / r ^ 2) x‖ ≤ D ^ k := by
      have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (n + 1)) =>
        hilbertQuadraticDerivativeBound_nonneg (H := H) r j) hmem
      have hleD : hilbertQuadraticDerivativeBound (H := H) r k ≤ D :=
        hsum.trans (le_add_of_nonneg_left zero_le_one)
      have hpow : D ≤ D ^ k := by simpa only [pow_one] using pow_le_pow_right₀ hD hk
      exact (hilbertQuadratic_iterated_bound c x r hx k).trans (hleD.trans hpow)
    exact norm_iteratedFDeriv_comp_le scalarUnitBump.contDiff
      ((contDiff_id.sub contDiff_const).norm_sq ℝ |>.div_const (r ^ 2)) (mod_cast le_top) x
      (fun k hk => hCbound k hk _) hDbound
  · have hsupport : tsupport (hilbertBump c r) ⊆ closedBall c r :=
      closure_minimal ((hilbertBump_support_subset c r hr).trans ball_subset_closedBall) isClosed_closedBall
    have hz : iteratedFDeriv ℝ n (hilbertBump c r) x = 0 := by
      apply notMem_support.mp
      intro hmem
      have hball := hsupport (support_iteratedFDeriv_subset n hmem)
      exact hx (by simpa only [mem_closedBall, dist_eq_norm] using hball)
    rw [hz, norm_zero]
    positivity

end

end GlobalRegularization
