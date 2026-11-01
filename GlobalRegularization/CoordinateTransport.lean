import GlobalRegularization.TriangularDerivativeConjugate
import GlobalRegularization.TriangularHomotopy

/-! Invariance of the ambient chart, affine isotopy and derivative
certificate under a continuous linear change of normed coordinates. -/

namespace GlobalRegularization

open Set
open scoped Topology

noncomputable section

variable {E F B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def C1Straightening.linear_transport (T : E ≃L[ℝ] F) (U : Set E)
    (D : F →L[ℝ] B) (f : E → B)
    (s : C1Straightening (T.symm ⁻¹' U) D (fun y => f (T.symm y))) :
    C1Straightening U (D.comp (T : E →L[ℝ] F)) f where
  target := T ⁻¹' s.target
  target_open := s.target_open.preimage T.continuous
  forward := fun x => T.symm (s.forward (T x))
  backward := fun y => T.symm (s.backward (T y))
  forward_maps := by
    intro x hx
    change T (T.symm (s.forward (T x))) ∈ s.target
    rw [T.apply_symm_apply]
    exact s.forward_maps (by simpa only [mem_preimage, T.symm_apply_apply] using hx)
  backward_maps := fun y hy => s.backward_maps hy
  left_inverse := by
    intro x hx
    rw [T.apply_symm_apply, s.left_inverse (T x) (by simpa only [mem_preimage, T.symm_apply_apply] using hx), T.symm_apply_apply]
  right_inverse := by
    intro y hy
    rw [T.apply_symm_apply, s.right_inverse (T y) hy, T.symm_apply_apply]
  forward_smooth := T.symm.contDiff.comp_contDiffOn (s.forward_smooth.comp T.contDiff.contDiffOn
    (fun x hx => by simpa only [mem_preimage, T.symm_apply_apply] using hx))
  backward_smooth := T.symm.contDiff.comp_contDiffOn
    (s.backward_smooth.comp T.contDiff.contDiffOn (fun y hy => hy))
  endpoint_identity := by
    intro x hx
    change D (T (T.symm (s.forward (T x)))) = D (T x) - f x
    rw [T.apply_symm_apply, s.endpoint_identity (T x) (by simpa only [mem_preimage, T.symm_apply_apply] using hx), T.symm_apply_apply]

theorem C1Straightening.linear_transport_isotopy (T : E ≃L[ℝ] F) (U : Set E)
    (D : F →L[ℝ] B) (f : E → B)
    (s : C1Straightening (T.symm ⁻¹' U) D (fun y => f (T.symm y)))
    (hi : s.HasAffineIsotopy) : (C1Straightening.linear_transport T U D f s).HasAffineIsotopy := by
  constructor
  · have hc : ContDiffOn ℝ 1 (fun p : ℝ × E => (p.1, T p.2)) (univ.prod U) :=
      contDiffOn_fst.prodMk (T.contDiff.comp_contDiffOn contDiffOn_snd)
    have hm : MapsTo (fun p : ℝ × E => (p.1, T p.2)) (univ.prod U) (univ.prod (T.symm ⁻¹' U)) := by
      intro p hp
      exact ⟨mem_univ _, by simpa only [mem_preimage, T.symm_apply_apply] using hp.2⟩
    have ht := T.symm.contDiff.comp_contDiffOn (hi.1.comp hc hm)
    simpa only [linear_transport, Function.comp_def, affineHomotopy, map_add, map_smul, map_sub,
      T.symm_apply_apply] using ht
  · intro a
    obtain ⟨slice, hs⟩ := hi.2 a
    refine ⟨C1Straightening.linear_transport T U D (fun x => a • f x) slice, ?_⟩
    funext x
    simp only [linear_transport, hs, affineHomotopy, map_add, map_smul, map_sub, T.symm_apply_apply]

end

end GlobalRegularization
