import GlobalRegularization.TriangularLimit
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! The exact finite telescoping identity that links the convergent shell
derivative series to the triangular operator theorem. -/

namespace GlobalRegularization

open Filter
open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def triangularDifferences (L : ℕ → E →L[ℝ] B) : ℕ → E →L[ℝ] B
  | 0 => -L 0
  | n + 1 => L n - L (n + 1)

def shellOperatorPartial (Q : ℕ → B →L[ℝ] E) (Lf : E →L[ℝ] B)
    (L : ℕ → E →L[ℝ] B) (n : ℕ) : E →L[ℝ] E :=
  -(Q 0).comp Lf + ∑ i ∈ Finset.range n, (Q i - Q (i + 1)).comp (Lf - L i)

theorem shellOperatorPartial_telescoping
    (Q : ℕ → B →L[ℝ] E) (Lf : E →L[ℝ] B) (L : ℕ → E →L[ℝ] B) (n : ℕ) :
    shellOperatorPartial Q Lf L n = triangularPartial Q (triangularDifferences L) (n + 1) +
      (Q n).comp (L n - Lf) := by
  induction n with
  | zero =>
      simp only [shellOperatorPartial, Finset.range_zero, Finset.sum_empty, add_zero,
        triangularPartial, Finset.sum_range_succ, triangularDifferences,
        ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_sub]
      abel
  | succ n ih =>
      have hs : shellOperatorPartial Q Lf L (n + 1) = shellOperatorPartial Q Lf L n +
          (Q n - Q (n + 1)).comp (Lf - L n) := by
        simp only [shellOperatorPartial, Finset.sum_range_succ]
        abel
      rw [hs, ih]
      simp only [triangularPartial, Finset.sum_range_succ, triangularDifferences,
        ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel

theorem triangularDifferences_annihilation
    (Q : ℕ → B →L[ℝ] E) (L : ℕ → E →L[ℝ] B)
    (hann : ∀ i j, i ≤ j → (L i).comp (Q j) = 0) :
    ∀ i j, i ≤ j → (triangularDifferences L i).comp (Q j) = 0 := by
  intro i j hij
  cases i with
  | zero => simp only [triangularDifferences, ContinuousLinearMap.neg_comp, hann 0 j (Nat.zero_le j), neg_zero]
  | succ i =>
      rw [triangularDifferences, ContinuousLinearMap.sub_comp, hann i j (by omega), hann (i + 1) j hij,
        sub_self]

theorem bounded_comp_tendsto_zero
    {Q : ℕ → B →L[ℝ] E} {L : ℕ → E →L[ℝ] B}
    (C : ℝ) (_hC : 0 ≤ C) (hQ : ∀ n, ‖Q n‖ ≤ C)
    (hL : Tendsto L atTop (𝓝 0)) :
    Tendsto (fun n => (Q n).comp (L n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun n => C * ‖L n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hL.norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hQ n) (norm_nonneg _))

theorem triangularPartial_tendsto_of_shell
    (Q : ℕ → B →L[ℝ] E) (Lf : E →L[ℝ] B) (L : ℕ → E →L[ℝ] B)
    (C : ℝ) (hC : 0 ≤ C) (hQ : ∀ n, ‖Q n‖ ≤ C)
    (hL : Tendsto L atTop (𝓝 Lf))
    (K : E →L[ℝ] E) (hK : Tendsto (shellOperatorPartial Q Lf L) atTop (𝓝 K)) :
    Tendsto (triangularPartial Q (triangularDifferences L)) atTop (𝓝 K) := by
  have hdiff : Tendsto (fun n => L n - Lf) atTop (𝓝 0) := by
    simpa only [sub_self] using hL.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => Lf) atTop (𝓝 Lf))
  have hrem := bounded_comp_tendsto_zero C hC hQ hdiff
  have heq (n : ℕ) : triangularPartial Q (triangularDifferences L) (n + 1) =
      shellOperatorPartial Q Lf L n - (Q n).comp (L n - Lf) := by
    rw [shellOperatorPartial_telescoping]
    abel
  have hshift : Tendsto (fun n => triangularPartial Q (triangularDifferences L) (n + 1))
      atTop (𝓝 K) := by
    simpa only [heq, sub_zero] using hK.sub hrem
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end

end GlobalRegularization
