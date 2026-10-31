import GlobalRegularization.ApproximationLimits

/-! Joint local approximation for uniformly bounded operators. This
includes the adapted history operators, which need not be contractions. -/

namespace GlobalRegularization

open Filter
open scoped Topology

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem linearApprox_joint_tendsto_bounded
    (P : ℕ → E →L[ℝ] E) (C : ℝ) (hP : ∀ n, ‖P n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) (x : E) :
    Tendsto (fun p : ℕ × E => P p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 x) := by
  have hy : Tendsto (fun p : ℕ × E => C * dist p.2 x) (atTop ×ˢ 𝓝 x) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_iff_dist_tendsto_zero.mp (tendsto_snd : Tendsto Prod.snd (atTop ×ˢ 𝓝 x) (𝓝 x))).const_mul C
  have hx : Tendsto (fun p : ℕ × E => dist (P p.1 x) x) (atTop ×ˢ 𝓝 x) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp ((hstrong x).comp tendsto_fst)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ (by simpa only [zero_add] using hy.add hx)
  intro p
  have hdiff : dist (P p.1 p.2) (P p.1 x) ≤ C * dist p.2 x :=
    ((P p.1).dist_le_opNorm p.2 x).trans (mul_le_mul_of_nonneg_right (hP p.1) dist_nonneg)
  exact (dist_triangle (P p.1 p.2) (P p.1 x) x).trans (add_le_add_right hdiff _)

theorem linearApprox_derivative_joint_tendsto_bounded
    (P : ℕ → E →L[ℝ] E) (C : ℝ) (hP : ∀ n, ‖P n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (D : E → E →L[ℝ] B) (x : E) (hD : ContinuousAt D x)
    (hfixed : Tendsto (fun n => (D x).comp (P n - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × E => (D (P p.1 p.2)).comp (P p.1) - D p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 0) := by
  let A : ℕ × E → E →L[ℝ] B := fun p => (D (P p.1 p.2) - D x).comp (P p.1)
  let R : ℕ × E → E →L[ℝ] B := fun p => D x - D p.2
  have hdP := hD.tendsto.comp (linearApprox_joint_tendsto_bounded P C hP hstrong x)
  have hdy : Tendsto (fun p : ℕ × E => D p.2) (atTop ×ˢ 𝓝 x) (𝓝 (D x)) :=
    hD.tendsto.comp tendsto_snd
  have hA : Tendsto A (atTop ×ˢ 𝓝 x) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hnorm : Tendsto (fun p : ℕ × E => ‖D (P p.1 p.2) - D x‖ * C)
        (atTop ×ˢ 𝓝 x) (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_mul] using
        ((hdP.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ × E => D x) _ (𝓝 (D x)))).norm).mul_const C
    apply squeeze_zero (fun _ => norm_nonneg _) _ hnorm
    intro p
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hP p.1) (norm_nonneg _))
  have hR : Tendsto R (atTop ×ˢ 𝓝 x) (𝓝 0) := by
    simpa only [R, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ × E => D x) _ (𝓝 (D x))).sub hdy
  have hB := hfixed.comp (tendsto_fst : Tendsto Prod.fst (atTop ×ˢ 𝓝 x) atTop)
  have heq (p : ℕ × E) : (D (P p.1 p.2)).comp (P p.1) - D p.2 =
      (A p + (D x).comp (P p.1 - ContinuousLinearMap.id ℝ E)) + R p := by
    ext z
    simp only [A, R, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  simpa only [heq, zero_add] using (hA.add hB).add hR

end GlobalRegularization
