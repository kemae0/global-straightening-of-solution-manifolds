import GlobalRegularization.ExtendedDerivative

/-! Transport of property (e) through bounded linear changes of histories,
continuous histories, and output coordinates. -/

namespace GlobalRegularization

open Set

variable {E F C D V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem HasExtendedDerivative.linear_pullback
    {U : Set E} (hU : IsOpen U) {ι : E →L[ℝ] C} {κ : F →L[ℝ] D} {f : E → V}
    (he : HasExtendedDerivative U ι f)
    (T : F →L[ℝ] E) (S : D →L[ℝ] C) (P : V →L[ℝ] W)
    (hcomm : ι.comp T = S.comp κ) :
    HasExtendedDerivative (T ⁻¹' U) κ (fun x => P (f (T x))) := by
  obtain ⟨ext, hagree, hcont⟩ := he.exists_extension
  have hc : ContDiffOn ℝ 1 (fun x => f (T x)) (T ⁻¹' U) :=
    he.c1.comp T.contDiff.contDiffOn (fun x hx => hx)
  refine ⟨P.contDiff.comp_contDiffOn hc, ⟨fun x => P.comp ((ext (T x)).comp S), ?_, ?_⟩⟩
  · intro x hx
    have hfx := ((he.c1.differentiableOn le_rfl (T x) hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hd := P.hasFDerivAt.comp x (hfx.comp x T.hasFDerivAt)
    calc
      _ = P.comp ((fderiv ℝ f (T x)).comp T) := hd.fderiv
      _ = (P.comp ((ext (T x)).comp S)).comp κ := by
        rw [hagree (T x) hx]
        simp only [ContinuousLinearMap.comp_assoc, hcomm]
  · have hmap : MapsTo (fun p : F × D => (T p.1, S p.2)) ((T ⁻¹' U).prod univ) (U.prod univ) :=
      fun p hp => ⟨hp.1, mem_univ _⟩
    have hcmap : Continuous (fun p : F × D => (T p.1, S p.2)) := by fun_prop
    exact P.continuous.comp_continuousOn (hcont.comp hcmap.continuousOn hmap)

end GlobalRegularization
