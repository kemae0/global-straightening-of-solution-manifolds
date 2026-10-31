import GlobalRegularization.MainStatement
import GlobalRegularization.TriangularHomotopy

/-! Transport of an already constructed localized chart under a genuine
bounded linear change of time. Stating the change abstractly keeps the
analytic construction and the elementary conjugation proof separate. -/

namespace GlobalRegularization

open Set
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def C1Straightening.time_transport
    (R : C1History h B ≃L[ℝ] C1History 1 B)
    (U : Set (C1History h B)) (f : C1History h B → B) (g : C1History 1 B → B) (r : ℝ)
    (hD : ∀ y, endpointDerivative h B (R.symm y) = r • endpointDerivative 1 B y)
    (hg : ∀ x, r • g (R x) = f x)
    (s : C1Straightening (R.symm ⁻¹' U) (endpointDerivative 1 B) g) :
    C1Straightening U (endpointDerivative h B) f := by
  have hRx (x : C1History h B) (hx : x ∈ U) : R x ∈ R.symm ⁻¹' U := by
    simpa only [mem_preimage, R.symm_apply_apply] using hx
  refine
    { target := R ⁻¹' s.target
      target_open := s.target_open.preimage R.continuous
      forward := fun x => R.symm (s.forward (R x))
      backward := fun y => R.symm (s.backward (R y))
      forward_maps := ?_
      backward_maps := fun y hy => s.backward_maps hy
      left_inverse := ?_
      right_inverse := ?_
      forward_smooth := R.symm.contDiff.comp_contDiffOn (s.forward_smooth.comp R.contDiff.contDiffOn hRx)
      backward_smooth := R.symm.contDiff.comp_contDiffOn
        (s.backward_smooth.comp R.contDiff.contDiffOn (fun y hy => hy))
      endpoint_identity := ?_ }
  · intro x hx
    change R (R.symm (s.forward (R x))) ∈ s.target
    rw [R.apply_symm_apply]
    exact s.forward_maps (hRx x hx)
  · intro x hx
    rw [R.apply_symm_apply, s.left_inverse (R x) (hRx x hx), R.symm_apply_apply]
  · intro y hy
    rw [R.apply_symm_apply, s.right_inverse (R y) hy, R.symm_apply_apply]
  · intro x hx
    rw [hD, s.endpoint_identity (R x) (hRx x hx), smul_sub]
    have hDx := hD (R x)
    rw [R.symm_apply_apply] at hDx
    rw [← hDx, hg]

def localizedStraightening_time_transport
    (R : C1History h B ≃L[ℝ] C1History 1 B)
    (q : HistoryInterval h → HistoryInterval 1)
    (U : Set (C1History h B)) (f : C1History h B → B) (g : C1History 1 B → B)
    (τ τ₁ ε r : ℝ)
    (hval : ∀ y t, historyInclusion h B (R.symm y) t = historyInclusion 1 B y (q t))
    (hzero : q (historyRight h) = historyRight 1)
    (hremote : ∀ t : HistoryInterval h, (t : ℝ) ≤ -τ → (q t : ℝ) ≤ -τ₁)
    (hD : ∀ y, endpointDerivative h B (R.symm y) = r • endpointDerivative 1 B y)
    (hg : ∀ x, r • g (R x) = f x)
    (hnorm : ∀ z, ‖historyInclusion h B (R.symm z)‖ ≤ ‖historyInclusion 1 B z‖)
    (s : LocalizedHistoryStraightening 1 B (R.symm ⁻¹' U) g τ₁ ε) :
    LocalizedHistoryStraightening h B U f τ ε := by
  have hRx (x : C1History h B) (hx : x ∈ U) : R x ∈ R.symm ⁻¹' U := by
    simpa only [mem_preimage, R.symm_apply_apply] using hx
  let A : C1History h B → C1History h B := fun x => R.symm (s.forward (R x))
  let Z : C1History h B → C1History h B := fun y => R.symm (s.backward (R y))
  let target := R ⁻¹' s.target
  have hAf : ContDiffOn ℝ 1 A U :=
    R.symm.contDiff.comp_contDiffOn (s.forward_smooth.comp R.contDiff.contDiffOn hRx)
  have hZf : ContDiffOn ℝ 1 Z target :=
    R.symm.contDiff.comp_contDiffOn (s.backward_smooth.comp R.contDiff.contDiffOn (fun y hy => hy))
  have hend : ∀ x ∈ U, endpointDerivative h B (A x) = endpointDerivative h B x - f x := by
    intro x hx
    change endpointDerivative h B (R.symm (s.forward (R x))) = _
    rw [hD, s.endpoint_identity (R x) (hRx x hx), smul_sub]
    have hDx := hD (R x)
    rw [R.symm_apply_apply] at hDx
    rw [← hDx, hg]
  let chart : C1Straightening U (endpointDerivative h B) f :=
    { target := target
      target_open := s.target_open.preimage R.continuous
      forward := A
      backward := Z
      forward_maps := by
        intro x hx
        change R (R.symm (s.forward (R x))) ∈ s.target
        rw [R.apply_symm_apply]
        exact s.forward_maps (hRx x hx)
      backward_maps := by
        intro y hy
        exact s.backward_maps hy
      left_inverse := by
        intro x hx
        change R.symm (s.backward (R (R.symm (s.forward (R x))))) = x
        rw [R.apply_symm_apply, s.left_inverse (R x) (hRx x hx), R.symm_apply_apply]
      right_inverse := by
        intro y hy
        change R.symm (s.forward (R (R.symm (s.backward (R y))))) = y
        rw [R.apply_symm_apply, s.right_inverse (R y) hy, R.symm_apply_apply]
      forward_smooth := hAf
      backward_smooth := hZf
      endpoint_identity := hend }
  refine { toC1Straightening := chart, preserves_zero := ?_, localized := ?_, uniform_small := ?_ }
  · intro x hx
    change historyInclusion h B (R.symm (s.forward (R x))) (historyRight h) = _
    rw [hval, hzero, s.preserves_zero (R x) (hRx x hx)]
    have hv := hval (R x) (historyRight h)
    rw [R.symm_apply_apply, hzero] at hv
    exact hv.symm
  · intro x hx t ht
    change historyInclusion h B (R.symm (s.forward (R x))) t = _
    rw [hval, s.localized (R x) (hRx x hx) _ (hremote t ht)]
    have hv := hval (R x) t
    rw [R.symm_apply_apply] at hv
    exact hv.symm
  · obtain ⟨c, hc, hsmall⟩ := s.uniform_small
    refine ⟨c, hc, ?_⟩
    intro x hx
    have heq : A x - x = R.symm (s.forward (R x) - R x) := by
      rw [map_sub, R.symm_apply_apply]
    change ‖historyInclusion h B (A x - x)‖ ≤ c
    rw [heq]
    exact (hnorm (s.forward (R x) - R x)).trans (hsmall (R x) (hRx x hx))

theorem localizedStraightening_time_transport_isotopy
    (R : C1History h B ≃L[ℝ] C1History 1 B)
    (q : HistoryInterval h → HistoryInterval 1)
    (U : Set (C1History h B)) (f : C1History h B → B) (g : C1History 1 B → B)
    (τ τ₁ ε r : ℝ)
    (hval : ∀ y t, historyInclusion h B (R.symm y) t = historyInclusion 1 B y (q t))
    (hzero : q (historyRight h) = historyRight 1)
    (hremote : ∀ t : HistoryInterval h, (t : ℝ) ≤ -τ → (q t : ℝ) ≤ -τ₁)
    (hD : ∀ y, endpointDerivative h B (R.symm y) = r • endpointDerivative 1 B y)
    (hg : ∀ x, r • g (R x) = f x)
    (hnorm : ∀ z, ‖historyInclusion h B (R.symm z)‖ ≤ ‖historyInclusion 1 B z‖)
    (s : LocalizedHistoryStraightening 1 B (R.symm ⁻¹' U) g τ₁ ε)
    (hiso : s.toC1Straightening.HasAffineIsotopy) :
    (localizedStraightening_time_transport h B R q U f g τ τ₁ ε r
      hval hzero hremote hD hg hnorm s).toC1Straightening.HasAffineIsotopy := by
  have hRx (x : C1History h B) (hx : x ∈ U) : R x ∈ R.symm ⁻¹' U := by
    simpa only [mem_preimage, R.symm_apply_apply] using hx
  constructor
  · have hc : ContDiffOn ℝ 1 (fun p : ℝ × C1History h B => (p.1, R p.2)) (univ.prod U) :=
      contDiffOn_fst.prodMk (R.contDiff.comp_contDiffOn contDiffOn_snd)
    have hm : MapsTo (fun p : ℝ × C1History h B => (p.1, R p.2)) (univ.prod U)
        (univ.prod (R.symm ⁻¹' U)) := fun p hp => ⟨mem_univ _, hRx p.2 hp.2⟩
    have ht := R.symm.contDiff.comp_contDiffOn (hiso.1.comp hc hm)
    change ContDiffOn ℝ 1 (fun p : ℝ × C1History h B =>
      p.2 + p.1 • (R.symm (s.forward (R p.2)) - p.2)) (univ.prod U)
    simpa only [Function.comp_def, affineHomotopy, map_add, map_smul, map_sub, R.symm_apply_apply] using ht
  · intro a
    obtain ⟨slice, hslice⟩ := hiso.2 a
    have hga : ∀ x, r • (a • g (R x)) = a • f x := by
      intro x
      rw [smul_comm, hg]
    let transported := C1Straightening.time_transport h B R U (fun x => a • f x)
      (fun y => a • g y) r hD hga slice
    refine ⟨transported, ?_⟩
    change (fun x => R.symm (slice.forward (R x))) =
      (fun x => x + a • (R.symm (s.forward (R x)) - x))
    rw [hslice]
    funext x
    simp only [affineHomotopy, map_add, map_smul, map_sub, R.symm_apply_apply]

end

end GlobalRegularization
