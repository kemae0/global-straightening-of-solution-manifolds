import GlobalRegularization.FiniteTriangular
import GlobalRegularization.OperatorTail
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Norm limits of triangular operator sums

This supplies the full finite-part/remainder argument from a convergent
series of actual operators. Nilpotence, annihilation of the remainder,
and convergence of the remainder are conclusions, not hypotheses.
-/

namespace GlobalRegularization

open Filter
open scoped Topology

noncomputable section

variable {𝕜 E B : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]

def triangularPartial (Q : ℕ → B →L[𝕜] E) (A : ℕ → E →L[𝕜] B) (n : ℕ) :
    E →L[𝕜] E := ∑ i ∈ Finset.range n, (Q i).comp (A i)

omit [CompleteSpace E] in
theorem triangularPartial_nilpotent
    (Q : ℕ → B →L[𝕜] E) (A : ℕ → E →L[𝕜] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0) (n : ℕ) :
    IsNilpotent (triangularPartial Q A n) := by
  have hm : ContinuousLinearMap.toLinearMapRingHom (triangularPartial Q A n) =
      finiteTriangle (fun i => (Q i).toLinearMap) (fun i => (A i).toLinearMap) n := by
    ext x
    simp [triangularPartial, finiteTriangle]
  have hn := finiteTriangle_pow_eq_zero
    (fun i => (Q i).toLinearMap) (fun i => (A i).toLinearMap) n
    (fun i j hi hij => by
      exact congrArg ContinuousLinearMap.toLinearMap (hann i j hij))
  refine ⟨n + 1, ?_⟩
  have hpow : ContinuousLinearMap.toLinearMapRingHom
      (triangularPartial Q A n ^ (n + 1)) = 0 := by rw [map_pow, hm, hn]
  ext x
  exact congrArg (fun L : Module.End 𝕜 E => L x) hpow

omit [CompleteSpace E] in
theorem triangularPartial_mul_term_eq_zero
    (Q : ℕ → B →L[𝕜] E) (A : ℕ → E →L[𝕜] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0)
    {n j : ℕ} (hnj : n ≤ j) :
    triangularPartial Q A n * (Q j).comp (A j) = 0 := by
  simp only [triangularPartial, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i ≤ j := (Finset.mem_range.mp hi).le.trans hnj
  change ((Q i).comp (A i)).comp ((Q j).comp (A j)) = 0
  rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc (Q i), hann i j hij]
  simp

omit [CompleteSpace E] in
theorem triangularPartial_annihilates_finite_tail
    (Q : ℕ → B →L[𝕜] E) (A : ℕ → E →L[𝕜] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0) (n m : ℕ) :
    triangularPartial Q A n *
      (triangularPartial Q A (n + m) - triangularPartial Q A n) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsum : triangularPartial Q A (n + (m + 1)) =
          triangularPartial Q A (n + m) + (Q (n + m)).comp (A (n + m)) := by
        exact Finset.sum_range_succ (fun i => (Q i).comp (A i)) (n + m)
      rw [hsum]
      have heq : triangularPartial Q A (n + m) + (Q (n + m)).comp (A (n + m)) -
          triangularPartial Q A n =
          (triangularPartial Q A (n + m) - triangularPartial Q A n) +
            (Q (n + m)).comp (A (n + m)) := by abel
      rw [heq, mul_add, ih, triangularPartial_mul_term_eq_zero Q A hann (by omega), zero_add]

omit [CompleteSpace E] in
theorem triangularPartial_annihilates_remainder
    (Q : ℕ → B →L[𝕜] E) (A : ℕ → E →L[𝕜] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0)
    (K : E →L[𝕜] E) (hK : Tendsto (triangularPartial Q A) atTop (𝓝 K)) (n : ℕ) :
    triangularPartial Q A n * (K - triangularPartial Q A n) = 0 := by
  have hshift : Tendsto (fun m => triangularPartial Q A (n + m)) atTop (𝓝 K) :=
    by simpa only [Nat.add_comm] using hK.comp (tendsto_add_atTop_nat n)
  have ht : Tendsto (fun m => triangularPartial Q A n *
      (triangularPartial Q A (n + m) - triangularPartial Q A n)) atTop
      (𝓝 (triangularPartial Q A n * (K - triangularPartial Q A n))) :=
    tendsto_const_nhds.mul (hshift.sub tendsto_const_nhds)
  have hz : Tendsto (fun m => triangularPartial Q A n *
      (triangularPartial Q A (n + m) - triangularPartial Q A n)) atTop (𝓝 0) := by
    simpa only [triangularPartial_annihilates_finite_tail Q A hann n] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E →L[𝕜] E)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hz

theorem isUnit_one_add_triangular_limit
    (Q : ℕ → B →L[𝕜] E) (A : ℕ → E →L[𝕜] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0)
    (K : E →L[𝕜] E) (hK : Tendsto (triangularPartial Q A) atTop (𝓝 K)) :
    IsUnit (1 + K) := by
  apply isUnit_one_add_of_nilpotent_approximation K (triangularPartial Q A)
    (fun n => K - triangularPartial Q A n)
  · intro n; abel
  · exact triangularPartial_nilpotent Q A hann
  · exact triangularPartial_annihilates_remainder Q A hann K hK
  · simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K)).sub hK

end

end GlobalRegularization
