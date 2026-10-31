import GlobalRegularization.ChartSubmersion
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Prod

/-! Actual global C¹ parametrizations of compatibility fibers by open
subsets of the split kernel, and the continuous finite-dimensional normal
frames. These give the claimed split-submanifold geometry. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

structure SplitC1FiberParametrization (U : Set E) (D : E →L[ℝ] B) (f : E → B) (b : B) where
  domain : Set (LinearMap.ker D)
  domain_open : IsOpen domain
  parameter : E → LinearMap.ker D
  realize : LinearMap.ker D → E
  parameter_smooth : ContDiffOn ℝ 1 parameter U
  realize_smooth : ContDiffOn ℝ 1 realize domain
  parameter_maps : ∀ x ∈ U, D x - f x = b → parameter x ∈ domain
  realize_maps : ∀ z ∈ domain, realize z ∈ U ∧ D (realize z) - f (realize z) = b
  left_inverse : ∀ x ∈ U, D x - f x = b → realize (parameter x) = x
  right_inverse : ∀ z ∈ domain, parameter (realize z) = z

def C1Straightening.splitFiberParametrization
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} (s : C1Straightening U D f)
    (Q : B →L[ℝ] E) (hQ : D.comp Q = ContinuousLinearMap.id ℝ B) (b : B) :
    SplitC1FiberParametrization U D f b := by
  have hright : Function.RightInverse Q D := fun a => congrArg (fun L : B →L[ℝ] B => L a) hQ
  let T := ContinuousLinearEquiv.equivOfRightInverse D Q hright
  let V := T '' s.target
  let W : Set (LinearMap.ker D) := (fun z => (b, z)) ⁻¹' V
  have htarget (z : LinearMap.ker D) (hz : z ∈ W) : T.symm (b, z) ∈ s.target := by
    obtain ⟨y, hy, heq⟩ := hz
    change T y = (b, z) at heq
    rw [← heq, T.symm_apply_apply]
    exact hy
  have hpair (x : E) (hx : x ∈ U) (hlevel : D x - f x = b) :
      (b, (T (s.forward x)).2) = T (s.forward x) := by
    apply Prod.ext
    · exact (s.endpoint_identity x hx |>.trans hlevel).symm
    · rfl
  have hDinv (z : LinearMap.ker D) : D (T.symm (b, z)) = b := by
    exact congrArg Prod.fst (T.apply_symm_apply (b, z))
  refine
    { domain := W
      domain_open := ((T.isOpenMap _ s.target_open).preimage (continuous_const.prodMk continuous_id))
      parameter := fun x => (T (s.forward x)).2
      realize := fun z => s.backward (T.symm (b, z))
      parameter_smooth := contDiff_snd.comp_contDiffOn (T.contDiff.comp_contDiffOn s.forward_smooth)
      realize_smooth := s.backward_smooth.comp
        (T.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)).contDiffOn htarget
      parameter_maps := ?_
      realize_maps := ?_
      left_inverse := ?_
      right_inverse := ?_ }
  · intro x hx hlevel
    change (b, (T (s.forward x)).2) ∈ V
    rw [hpair x hx hlevel]
    exact ⟨s.forward x, s.forward_maps hx, rfl⟩
  · intro z hz
    refine ⟨s.backward_maps (htarget z hz), ?_⟩
    have he := s.endpoint_identity (s.backward (T.symm (b, z))) (s.backward_maps (htarget z hz))
    rw [s.right_inverse _ (htarget z hz), hDinv] at he
    exact he.symm
  · intro x hx hlevel
    rw [hpair x hx hlevel, T.symm_apply_apply, s.left_inverse x hx]
  · intro z hz
    rw [s.right_inverse _ (htarget z hz), T.apply_symm_apply]

theorem isCompl_ker_range_of_rightInverse (D : E →L[ℝ] B) (R : B →L[ℝ] E)
    (hDR : D.comp R = ContinuousLinearMap.id ℝ B) :
    IsCompl (LinearMap.ker D) (LinearMap.range R) := by
  have hr (b : B) : D (R b) = b := congrArg (fun L : B →L[ℝ] B => L b) hDR
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨b, rfl⟩
    change D (R b) = 0 at hx
    rw [hr] at hx
    rw [hx, map_zero]
  · rw [codisjoint_iff_le_sup]
    intro x hx
    rw [Submodule.mem_sup]
    refine ⟨x - R (D x), ?_, R (D x), ⟨D x, rfl⟩, by abel⟩
    change D (x - R (D x)) = 0
    rw [map_sub, hr, sub_self]

theorem C1Straightening.continuous_complement_family
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} (s : C1Straightening U D f)
    (hU : IsOpen U) (Q : B →L[ℝ] E) (hQ : D.comp Q = ContinuousLinearMap.id ℝ B) :
    ContinuousOn (s.defectRightInverse Q) U ∧ ∀ x ∈ U,
      IsCompl (LinearMap.ker (fderiv ℝ (fun y => D y - f y) x))
        (LinearMap.range (s.defectRightInverse Q x)) := by
  exact ⟨s.defectRightInverse_continuousOn Q, fun x hx =>
    isCompl_ker_range_of_rightInverse _ _ (s.defectRightInverse_spec hU Q hQ hx)⟩

theorem C1Straightening.normal_dimension
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} (s : C1Straightening U D f)
    [FiniteDimensional ℝ B] (hU : IsOpen U) (Q : B →L[ℝ] E)
    (hQ : D.comp Q = ContinuousLinearMap.id ℝ B) {x : E} (hx : x ∈ U) :
    Module.finrank ℝ (LinearMap.range (s.defectRightInverse Q x)) = Module.finrank ℝ B ∧
      Module.finrank ℝ (E ⧸ LinearMap.ker (fderiv ℝ (fun y => D y - f y) x)) = Module.finrank ℝ B := by
  let R := s.defectRightInverse Q x
  let F := fderiv ℝ (fun y => D y - f y) x
  have hright : Function.RightInverse R F := fun b => congrArg (fun L : B →L[ℝ] B => L b)
    (s.defectRightInverse_spec hU Q hQ hx)
  exact ⟨LinearMap.finrank_range_of_inj hright.injective,
    (F.toLinearMap.quotKerEquivOfSurjective hright.surjective).finrank_eq⟩

end

end GlobalRegularization
