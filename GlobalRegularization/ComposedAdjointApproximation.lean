import GlobalRegularization.DenseDualApproximation

namespace GlobalRegularization

open Filter
open scoped Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem composed_adjoint_contractions_tendsto
    (T P : ℕ → E →L[ℝ] E) (hP : ∀ n, ‖P n‖ ≤ 1) (L : E →L[ℝ] V)
    (hT : Tendsto (fun n => L.comp (T n - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0))
    (hV : Tendsto (fun n => L.comp (P n - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0)) :
    Tendsto (fun n => L.comp ((T n).comp (P n) - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0) := by
  have hf : Tendsto (fun n => (L.comp (T n - ContinuousLinearMap.id ℝ E)).comp (P n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa only [norm_zero] using hT.norm)
    intro n
    have hm := mul_le_mul_of_nonneg_left (hP n) (norm_nonneg (L.comp (T n - ContinuousLinearMap.id ℝ E)))
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by simpa only [mul_one] using hm)
  have heq (n : ℕ) : L.comp ((T n).comp (P n) - ContinuousLinearMap.id ℝ E) =
      (L.comp (T n - ContinuousLinearMap.id ℝ E)).comp (P n) +
        L.comp (P n - ContinuousLinearMap.id ℝ E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  simpa only [heq, zero_add] using hf.add hV

end GlobalRegularization
