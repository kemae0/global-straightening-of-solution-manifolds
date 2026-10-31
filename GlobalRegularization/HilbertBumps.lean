import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

/-! Actual bounded smooth radial bumps on arbitrary real Hilbert spaces,
with globally bounded first derivatives. No compactness of Hilbert balls
is used. -/

namespace GlobalRegularization

open Set Filter Metric Function
open scoped Topology ContDiff

noncomputable section

def scalarUnitBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1 / 4, rOut := 1, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def hilbertBump (c : H) (r : ℝ) (x : H) : ℝ := scalarUnitBump (‖x - c‖ ^ 2 / r ^ 2)

theorem hilbertBump_contDiff (c : H) (r : ℝ) : ContDiff ℝ ∞ (hilbertBump c r) :=
  scalarUnitBump.contDiff.comp ((contDiff_id.sub contDiff_const).norm_sq ℝ |>.div_const (r ^ 2))

omit [InnerProductSpace ℝ H] in
theorem hilbertBump_nonneg (c : H) (r : ℝ) (x : H) : 0 ≤ hilbertBump c r x := scalarUnitBump.nonneg

omit [InnerProductSpace ℝ H] in
theorem hilbertBump_le_one (c : H) (r : ℝ) (x : H) : hilbertBump c r x ≤ 1 := scalarUnitBump.le_one

omit [InnerProductSpace ℝ H] in
theorem hilbertBump_support_subset (c : H) (r : ℝ) (hr : 0 < r) :
    support (hilbertBump c r) ⊆ ball c r := by
  intro x hx
  have hu : ‖x - c‖ ^ 2 / r ^ 2 ∈ support scalarUnitBump := hx
  rw [ContDiffBump.support_eq] at hu
  change dist (‖x - c‖ ^ 2 / r ^ 2) 0 < 1 at hu
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hu
  have hs := (div_lt_iff₀ (sq_pos_of_pos hr)).mp hu
  rw [mem_ball, dist_eq_norm]
  nlinarith [norm_nonneg (x - c)]

omit [InnerProductSpace ℝ H] in
theorem hilbertBump_one_of_dist_le (c : H) (r : ℝ) (hr : 0 < r) (x : H)
    (hx : dist x c ≤ r / 2) : hilbertBump c r x = 1 := by
  apply scalarUnitBump.one_of_mem_closedBall
  change dist (‖x - c‖ ^ 2 / r ^ 2) 0 ≤ 1 / 4
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  rw [dist_eq_norm] at hx
  nlinarith [norm_nonneg (x - c)]

theorem hilbertBump_derivative_bound (c : H) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (hilbertBump c r) x‖ ≤ C := by
  obtain ⟨M, hM⟩ := scalarUnitBump.hasCompactSupport.deriv.exists_bound_of_continuous
    (scalarUnitBump.contDiff.of_le (show (1 : ℕ∞) ≤ ∞ by simp)).continuous_deriv_one
  let D := max 0 M
  have hD : 0 ≤ D := le_max_left _ _
  refine ⟨D * ((r ^ 2)⁻¹ * (2 * r)), by positivity, ?_⟩
  intro x
  let u := ‖x - c‖ ^ 2 / r ^ 2
  have hg := (((hasFDerivAt_id x).sub_const c).norm_sq).const_smul ((r ^ 2)⁻¹)
  have hg' : HasFDerivAt (fun y : H => ‖y - c‖ ^ 2 / r ^ 2)
      ((r ^ 2)⁻¹ • ((2 : ℝ) • innerSL ℝ (x - c))) x := by
    simpa only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul, id,
      ContinuousLinearMap.comp_id, two_smul] using hg
  have hb := ((scalarUnitBump.contDiff.of_le (show (1 : ℕ∞) ≤ ∞ by simp)).differentiable_one u).hasDerivAt
  have hd := hb.comp_hasFDerivAt x hg'
  have heq : fderiv ℝ (hilbertBump c r) x =
      deriv scalarUnitBump u • ((r ^ 2)⁻¹ • ((2 : ℝ) • innerSL ℝ (x - c))) := by
    exact hd.fderiv
  rw [heq]
  by_cases hx : ‖x - c‖ ≤ r
  · rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)), abs_of_pos (by norm_num : (0 : ℝ) < 2),
      innerSL_apply_norm]
    have hbnd : ‖deriv scalarUnitBump u‖ ≤ D := (hM u).trans (le_max_right _ _)
    rw [← Real.norm_eq_abs]
    gcongr
  · have hu : 1 < u := by
      apply (lt_div_iff₀ (sq_pos_of_pos hr)).mpr
      have hx' := lt_of_not_ge hx
      nlinarith [norm_nonneg (x - c)]
    have hz : deriv scalarUnitBump u = 0 := by
      apply notMem_support.mp
      intro hmem
      have ht := support_deriv_subset hmem
      rw [ContDiffBump.tsupport_eq] at ht
      change dist u 0 ≤ 1 at ht
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)] at ht
      linarith
    rw [hz, zero_smul, norm_zero]
    positivity

theorem exists_hilbert_C1_bump_in_nhds {s : Set H} {x : H} (hs : s ∈ 𝓝 x) :
    ∃ f : H → ℝ, support f ⊆ s ∧ ContDiff ℝ 1 f ∧
      (∀ y, f y ∈ Icc 0 1) ∧ f x = 1 ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ f y‖ ≤ C := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨hilbertBump x r, (hilbertBump_support_subset x r hr).trans hball,
    (hilbertBump_contDiff x r).of_le (by simp),
    fun y => ⟨hilbertBump_nonneg x r y, hilbertBump_le_one x r y⟩, ?_,
    hilbertBump_derivative_bound x r hr⟩
  exact hilbertBump_one_of_dist_le x r hr x (by simp; positivity)

end

end GlobalRegularization
