import GlobalRegularization.ApproximationLimits
import GlobalRegularization.CylindricalFamily

/-! The tolerance-dependent local `C¹` approximation in operator norm,
derived from the constructed cylindrical cutoffs and the observation
approximation. This is not merely pointwise convergence of derivatives. -/

namespace GlobalRegularization

open Set Filter Metric
open scoped Topology

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def LocalC1Approximation (U : Set E) (f : E → B) (fm : ℕ → E → B) : Prop :=
  ∀ x ∈ U, ∀ η > 0, ∃ r > 0, ball x r ⊆ U ∧ ∃ N : ℕ,
    ∀ n ≥ N, ∀ y ∈ ball x r,
      ‖fm n y - f y‖ + ‖fderiv ℝ (fm n) y - fderiv ℝ f y‖ < η

omit [NormedSpace ℝ E] in
theorem eventually_prod_has_ball {x : E} {q : ℕ × E → Prop}
    (hq : ∀ᶠ p in atTop ×ˢ 𝓝 x, q p) :
    ∃ r > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x r, q (n, y) := by
  obtain ⟨pa, hpa, pb, hpb, hrect⟩ := eventually_prod_iff.mp hq
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpa
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpb
  exact ⟨r, hr, N, fun n hn y hy => hrect (hN n hn) (hball hy)⟩

theorem localC1Approximation_of_agreement
    {U : Set E} (hU : IsOpen U) (f : E → B) (hf : ContDiffOn ℝ 1 f U)
    (P : ℕ → E →L[ℝ] E) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hfixed : ∀ x ∈ U, Tendsto (fun n => (fderiv ℝ f x).comp
      (P n - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0))
    (fm : ℕ → E → B)
    (hagree : ∀ x ∈ U, ∃ r > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x r, fm n y = f (P n y)) :
    LocalC1Approximation U f fm := by
  intro x hx η hη
  let L : Filter (ℕ × E) := atTop ×ˢ 𝓝 x
  obtain ⟨r₀, hr₀, N₀, hlocal⟩ := hagree x hx
  have hidx : ∀ᶠ p : ℕ × E in L, N₀ ≤ p.1 := tendsto_fst.eventually (eventually_ge_atTop N₀)
  have hball : ∀ᶠ p : ℕ × E in L, p.2 ∈ ball x r₀ :=
    tendsto_snd.eventually (ball_mem_nhds x hr₀)
  have hpx := linearApprox_joint_tendsto P hP hstrong x
  have hinside : ∀ᶠ p : ℕ × E in L, P p.1 p.2 ∈ U := hpx.eventually (hU.mem_nhds hx)
  have hvalEq : (fun p : ℕ × E => fm p.1 p.2 - f p.2) =ᶠ[L]
      (fun p => f (P p.1 p.2) - f p.2) := by
    filter_upwards [hidx, hball] with p hn hy
    rw [hlocal p.1 hn p.2 hy]
  have hderEq : (fun p : ℕ × E => fderiv ℝ (fm p.1) p.2 - fderiv ℝ f p.2) =ᶠ[L]
      (fun p => (fderiv ℝ f (P p.1 p.2)).comp (P p.1) - fderiv ℝ f p.2) := by
    filter_upwards [hidx, hball, hinside] with p hn hy hpU
    have heq : fm p.1 =ᶠ[𝓝 p.2] (fun y => f (P p.1 y)) :=
      mem_of_superset (isOpen_ball.mem_nhds hy) (fun y hyy => hlocal p.1 hn y hyy)
    have hdf := (hf.contDiffAt (hU.mem_nhds hpU)).differentiableAt le_rfl
    have hcomp := hdf.hasFDerivAt.comp p.2 (P p.1).hasFDerivAt
    rw [heq.fderiv_eq]
    exact congrArg (fun D : E →L[ℝ] B => D - fderiv ℝ f p.2) hcomp.fderiv
  have hfc : ContinuousAt f x := hf.continuousOn.continuousAt (hU.mem_nhds hx)
  have hv : Tendsto (fun p : ℕ × E => fm p.1 p.2 - f p.2) L (𝓝 0) := by
    apply (tendsto_congr' hvalEq).mpr
    simpa only [sub_self] using (hfc.tendsto.comp hpx).sub (hfc.tendsto.comp tendsto_snd)
  have hD : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx)
  have hd : Tendsto (fun p : ℕ × E => fderiv ℝ (fm p.1) p.2 - fderiv ℝ f p.2) L (𝓝 0) :=
    (tendsto_congr' hderEq).mpr
      (linearApprox_derivative_joint_tendsto P hP hstrong (fderiv ℝ f) x hD (hfixed x hx))
  have hnorm : Tendsto (fun p : ℕ × E =>
      ‖fm p.1 p.2 - f p.2‖ + ‖fderiv ℝ (fm p.1) p.2 - fderiv ℝ f p.2‖) L (𝓝 0) := by
    simpa only [norm_zero, zero_add] using hv.norm.add hd.norm
  have hsmall := (tendsto_order.mp hnorm).2 η hη
  have hyU : ∀ᶠ p : ℕ × E in L, p.2 ∈ U := tendsto_snd.eventually (hU.mem_nhds hx)
  obtain ⟨r, hr, N, hrect⟩ := eventually_prod_has_ball (hsmall.and hyU)
  refine ⟨r, hr, ?_, N, ?_⟩
  · intro y hy
    exact (hrect N le_rfl y hy).2
  · intro n hn y hy
    exact (hrect n hn y hy).1

theorem exists_bounded_local_C1_cylindrical_family
    (U : Set E) (hU : IsOpen U) (f : E → B) (hf : ContDiffOn ℝ 1 f U)
    (P : ℕ → E →L[ℝ] E) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hfinite : ∀ n, FiniteDimensional ℝ (LinearMap.range (P n)))
    (hfixed : ∀ x ∈ U, Tendsto (fun n => (fderiv ℝ f x).comp
      (P n - ContinuousLinearMap.id ℝ E)) atTop (𝓝 0)) :
    ∃ fm : ℕ → E → B, (∀ n, ContDiff ℝ 1 (fm n)) ∧
      (∀ n, Bornology.IsBounded (range (fm n))) ∧
      (∀ n, ∃ hat : LinearMap.range (P n) → B, ContDiff ℝ 1 hat ∧
        ∀ x, fm n x = hat ((P n).rangeRestrict x)) ∧ LocalC1Approximation U f fm := by
  obtain ⟨fm, hsmooth, hbounded, hfactor, hagree⟩ :=
    exists_bounded_cylindrical_family U hU f hf P hP hstrong hfinite
  exact ⟨fm, hsmooth, hbounded, hfactor,
    localC1Approximation_of_agreement hU f hf P hP hstrong hfixed fm hagree⟩

end GlobalRegularization
