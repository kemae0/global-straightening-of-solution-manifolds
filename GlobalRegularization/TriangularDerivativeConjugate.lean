import GlobalRegularization.TriangularDerivative

/-! The actual triangular derivative certificate is preserved by bounded
linear changes of coordinates, including changes of history time scale. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E F B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem C1Straightening.HasTriangularDerivative.conjugate
    {U : Set E} {V : Set F} {D : E →L[ℝ] B} {D' : F →L[ℝ] B} {f : E → B} {g : F → B}
    (s : C1Straightening V D' g) (hs : s.HasTriangularDerivative) (hV : IsOpen V)
    (T : E ≃L[ℝ] F) (chart : C1Straightening U D f)
    (hdom : ∀ x ∈ U, T x ∈ V)
    (hforward : chart.forward = fun x => T.symm (s.forward (T x))) : chart.HasTriangularDerivative := by
  intro x hx
  obtain ⟨Q, A, hann, hlim⟩ := hs (T x) (hdom x hx)
  let Q' := fun i => (T.symm : F →L[ℝ] E).comp (Q i)
  let A' := fun i => (A i).comp (T : E →L[ℝ] F)
  refine ⟨Q', A', ?_, ?_⟩
  · intro i j hij
    ext a
    have hz := congrArg (fun L : B →L[ℝ] B => L a) (hann i j hij)
    change A i (T (T.symm (Q j a))) = 0
    rw [T.apply_symm_apply]
    exact hz
  · have hdf := (s.forward_smooth.contDiffAt (hV.mem_nhds (hdom x hx))).differentiableAt le_rfl
    have hd := T.symm.hasFDerivAt.comp x (hdf.hasFDerivAt.comp x T.hasFDerivAt)
    have hD : fderiv ℝ chart.forward x = (T.symm : F →L[ℝ] E).comp
        ((fderiv ℝ s.forward (T x)).comp (T : E →L[ℝ] F)) := by
      simpa only [hforward, Function.comp_def] using hd.fderiv
    have heq (n : ℕ) : triangularPartial Q' A' n = (T.symm : F →L[ℝ] E).comp
        ((triangularPartial Q A n).comp (T : E →L[ℝ] F)) := by
      ext y
      simp only [triangularPartial, Q', A', ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply, map_sum]
    have hc : Continuous (fun L : F →L[ℝ] F => (T.symm : F →L[ℝ] E).comp (L.comp (T : E →L[ℝ] F))) := by
      fun_prop
    have ht := (hc.tendsto (fderiv ℝ s.forward (T x) - 1)).comp hlim
    have he : (T.symm : F →L[ℝ] E).comp
        ((fderiv ℝ s.forward (T x) - 1).comp (T : E →L[ℝ] F)) = fderiv ℝ chart.forward x - 1 := by
      rw [hD]
      ext y
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub,
        ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    rw [he] at ht
    exact (tendsto_congr heq).mpr ht

end

end GlobalRegularization
