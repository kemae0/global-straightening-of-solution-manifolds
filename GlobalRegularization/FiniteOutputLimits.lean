import GlobalRegularization.VectorRieszRepresentation
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Operator-norm convergence into a finite product, from convergence of
the scalar coordinate operators. -/

namespace GlobalRegularization

open Filter
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteOutputCLM_expansion (n : ℕ) (L : E →L[ℝ] (Fin n → ℝ)) :
    L = ∑ i : Fin n, (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i).comp
      ((ContinuousLinearMap.proj i).comp L) := by
  classical
  ext x j
  simp [Pi.single_apply]

theorem finiteOutputCLM_tendsto_zero (n : ℕ) (L : ℕ → E →L[ℝ] (Fin n → ℝ))
    (hL : ∀ i : Fin n, Tendsto (fun m => (ContinuousLinearMap.proj i).comp (L m))
      atTop (𝓝 0)) : Tendsto L atTop (𝓝 0) := by
  have ht (i : Fin n) := ((ContinuousLinearMap.compL ℝ E ℝ (Fin n → ℝ)
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i)).continuous.tendsto 0).comp (hL i)
  have hs := tendsto_finset_sum Finset.univ (fun i hi => ht i)
  simpa only [Function.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_zero,
    Finset.sum_const_zero, ← finiteOutputCLM_expansion] using hs

theorem tendsto_clm_comp_const_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : ℕ → V →L[ℝ] W) (hL : Tendsto L atTop (𝓝 0)) (D : E →L[ℝ] V) :
    Tendsto (fun m => (L m).comp D) atTop (𝓝 0) := by
  have ht := ((continuous_id.clm_comp_const D).tendsto (0 : V →L[ℝ] W)).comp hL
  simpa only [ContinuousLinearMap.zero_comp] using ht

end

end GlobalRegularization
