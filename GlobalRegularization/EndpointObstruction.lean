import GlobalRegularization.ChartSubmersion
import GlobalRegularization.HistorySpace

/-! The endpoint-identity obstruction with its necessary nonempty-domain
and nontrivial-state hypotheses, and the empty-domain counterexample. -/

namespace GlobalRegularization

open Set
open scoped NNReal

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem no_endpoint_identity_straightening [Nontrivial B]
    (U : Set E) (hU : IsOpen U) (hne : U.Nonempty)
    (D : E →L[ℝ] B) (Q : B →L[ℝ] E) (hQ : D.comp Q = ContinuousLinearMap.id ℝ B) :
    ¬ Nonempty (C1Straightening U D (fun x => D x)) := by
  rintro ⟨chart⟩
  obtain ⟨x, hx⟩ := hne
  have hr := chart.defectRightInverse_spec hU Q hQ hx
  have hz : fderiv ℝ (fun y => D y - D y) x = 0 := by
    simpa only [sub_self] using (hasFDerivAt_const (𝕜 := ℝ) (0 : B) x).fderiv
  rw [hz, ContinuousLinearMap.zero_comp] at hr
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  have h := congrArg (fun L : B →L[ℝ] B => L b) hr
  exact hb h.symm

def emptyDomainStraightening (D : E →L[ℝ] B) (f : E → B) : C1Straightening ∅ D f where
  target := ∅
  target_open := isOpen_empty
  forward := id
  backward := id
  forward_maps := fun _ hx => hx
  backward_maps := fun _ hx => hx
  left_inverse := fun _ _ => rfl
  right_inverse := fun _ _ => rfl
  forward_smooth := contDiff_id.contDiffOn
  backward_smooth := contDiff_id.contDiffOn
  endpoint_identity := fun _ hx => False.elim hx

theorem empty_domain_endpoint_identity_straightening (D : E →L[ℝ] B) :
    Nonempty (C1Straightening ∅ D (fun x => D x)) := ⟨emptyDomainStraightening D D⟩

def endpointIdentityStraighteningOfSubsingleton [Subsingleton B] (U : Set E) (hU : IsOpen U)
    (D : E →L[ℝ] B) : C1Straightening U D (fun x => D x) where
  target := U
  target_open := hU
  forward := id
  backward := id
  forward_maps := fun _ hx => hx
  backward_maps := fun _ hx => hx
  left_inverse := fun _ _ => rfl
  right_inverse := fun _ _ => rfl
  forward_smooth := contDiff_id.contDiffOn
  backward_smooth := contDiff_id.contDiffOn
  endpoint_identity := fun _ _ => Subsingleton.elim _ _

end

end GlobalRegularization
