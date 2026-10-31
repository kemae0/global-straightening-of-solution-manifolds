import GlobalRegularization.RealComplexification

/-! The complexification contains an isometric real copy of E, every
element is x + i y, and the extension of a real operator is unique. -/

namespace GlobalRegularization.RealComplexification

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_embed (x : E) : ‖embed x‖ = ‖x‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
    intro z
    change ‖z.re • x‖ ≤ ‖x‖ * ‖z‖
    rw [norm_smul, Real.norm_eq_abs, mul_comm ‖x‖ ‖z‖]
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg x)
  · have hn := (embed x : ℂ →L[ℝ] E).le_opNorm (1 : ℂ)
    change ‖(1 : ℂ).re • x‖ ≤ ‖embed x‖ * ‖(1 : ℂ)‖ at hn
    simpa only [Complex.one_re, one_smul, norm_one, mul_one] using hn

theorem decomposition (f : RealComplexification E) :
    f = embed (f 1) + Complex.I • embed (-(f Complex.I)) := by
  ext z
  let ff : ℂ →L[ℝ] E := f
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by apply Complex.ext <;> simp
  have hfz : f z = z.re • f 1 + z.im • f Complex.I := by
    calc
      _ = (f : ℂ →L[ℝ] E) (z.re • (1 : ℂ) + z.im • Complex.I) :=
        congrArg (fun w => f w) hz
      _ = ff (z.re • (1 : ℂ)) + ff (z.im • Complex.I) := _root_.map_add ff _ _
      _ = _ := congrArg₂ (fun a b : E => a + b) (_root_.map_smul ff _ _) (_root_.map_smul ff _ _)
  rw [hfz]
  simp only [add_apply, complex_smul_apply, embed_apply, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_smul, smul_neg, neg_neg]

theorem map_unique (L : E →L[ℝ] F)
    (T : RealComplexification E →L[ℂ] RealComplexification F)
    (hT : ∀ x, T (embed x) = embed (L x)) : T = map L := by
  apply ContinuousLinearMap.ext
  intro f
  conv_lhs => rw [decomposition f]
  conv_rhs => rw [decomposition f]
  rw [T.map_add, T.map_smul, (map L).map_add, (map L).map_smul, hT, hT, map_embed, map_embed]

end

end GlobalRegularization.RealComplexification
