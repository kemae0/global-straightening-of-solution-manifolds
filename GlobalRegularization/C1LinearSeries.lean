import GlobalRegularization.LocallyVanishingSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Continuous differentiability of a locally convergent shell series,
including its exact derivative series. The local uniform convergence is
proved from maximum estimates, rather than postulated. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {D V F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem C1_linear_series_of_locally_vanishing
    {U : Set D} (hU : IsOpen U)
    (S : ℕ → V →L[ℝ] F) (K : ℝ) (hK : 0 < K)
    (hbound : HasMaxFiniteSumBound S K)
    (hboundD : HasMaxFiniteSumBound
      (fun n => ContinuousLinearMap.compL ℝ D V F (S n)) K)
    (a : ℕ → D → V) (da : ℕ → D → D →L[ℝ] V)
    (ha : LocallyVanishing U a) (hda : LocallyVanishing U da)
    (hd : ∀ n x, x ∈ U → HasFDerivAt (a n) (da n x) x)
    (hc : ∀ n, ContinuousOn (da n) U) :
    ContDiffOn ℝ 1 (fun x => ∑' n, S n (a n x)) U ∧
      ∀ x ∈ U, HasFDerivAt (fun y => ∑' n, S n (a n y))
        (∑' n, (S n).comp (da n x)) x := by
  let SD := fun n => ContinuousLinearMap.compL ℝ D V F (S n)
  have hconvD := locally_uniform_linear_series_of_locally_vanishing SD K hK hboundD da hda
  have hcontD := continuousOn_linear_series_of_locally_vanishing SD K hK hboundD da hda hc
  have hparts : ∀ N x, x ∈ U → HasFDerivAt
      (fun y => ∑ n ∈ Finset.range N, S n (a n y))
      (∑ n ∈ Finset.range N, SD n (da n x)) x := by
    intro N x hx
    exact HasFDerivAt.fun_sum (fun n hn => (S n).hasFDerivAt.comp x (hd n x hx))
  have hpoint : ∀ x ∈ U, Tendsto (fun N => ∑ n ∈ Finset.range N, S n (a n x))
      atTop (𝓝 (∑' n, S n (a n x))) := by
    intro x hx
    exact (summable_linear_series_of_locally_vanishing S K hK hbound a ha hx).hasSum.tendsto_sum_nat
  have hlim : ∀ x ∈ U, HasFDerivAt (fun y => ∑' n, S n (a n y))
      (∑' n, (S n).comp (da n x)) x := by
    intro x hx
    exact hasFDerivAt_of_tendstoLocallyUniformlyOn hU hconvD hparts hpoint hx
  refine ⟨?_, hlim⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU).mpr
  refine ⟨?_, by simp, ?_⟩
  · intro x hx
    exact (hlim x hx).differentiableAt.differentiableWithinAt
  · apply contDiffOn_zero.mpr
    exact hcontD.congr (fun x hx => (hlim x hx).fderiv)

end

end GlobalRegularization
