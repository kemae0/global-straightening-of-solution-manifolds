import GlobalRegularization.TerminalExistence
import GlobalRegularization.EndpointCoupling
import GlobalRegularization.ChartSubmersion

/-! Level sets and endpoint coupling under the stronger terminal-atom
hypothesis, with no property-(e) assumption. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

theorem terminal_atom_all_levels
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      ∀ b : Fin n → ℝ, chart.forward '' {x | x ∈ U ∧ endpointDerivative h (Fin n → ℝ) x - f x = b} =
        (chart.forward '' U) ∩ {y | endpointDerivative h (Fin n → ℝ) y = b} := by
  obtain ⟨chart⟩ := terminal_atom_localized_straightening h hh n U hU f hf hzero τ ε hτ hε
  exact ⟨chart, fun b => c1_straightening_all_levels U (endpointDerivative h (Fin n → ℝ)) f chart.toC1Straightening b⟩

theorem terminal_atom_endpoint_coupling
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (g : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hg : ContDiffOn ℝ 1 g U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U g)
    (M : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (N : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hN : (N : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = ContinuousLinearMap.id ℝ (Fin n → ℝ) - M) :
    Nonempty (C1Straightening U (endpointDerivative h (Fin n → ℝ))
      (fun x => M (endpointDerivative h (Fin n → ℝ) x) + g x)) := by
  let gt : C1History h (Fin n → ℝ) → (Fin n → ℝ) := fun x => N.symm (g x)
  have hgt : ContDiffOn ℝ 1 gt U := N.symm.contDiff.comp_contDiffOn hg
  have hzt : HasVanishingTerminalDerivative h (Fin n → ℝ) U gt := by
    intro x hx δ hδ hlim
    have hD : fderiv ℝ gt x = (N.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).comp (fderiv ℝ g x) :=
      (N.symm.hasFDerivAt.comp x ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt le_rfl).hasFDerivAt).fderiv
    have ht := ((ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) (Fin n → ℝ)
      (N.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))).continuous.tendsto 0).comp (hzero x hx δ hδ hlim)
    simpa only [hD, Function.comp_apply, ContinuousLinearMap.compL_apply, map_zero,
      ContinuousLinearMap.comp_assoc] using ht
  obtain ⟨s⟩ := terminal_atom_localized_straightening h hh n U hU gt hgt hzt ((h : ℝ) / 2) 1
    (by positivity) zero_lt_one
  let Q := terminalCorrection h (Fin n → ℝ) 1 zero_lt_one
  let chart := s.toC1Straightening.postcompose_endpoint Q
    (terminalCorrection_endpoint h (Fin n → ℝ) 1 zero_lt_one) N
  have heq : (fun x => endpointDerivative h (Fin n → ℝ) x - N (endpointDerivative h (Fin n → ℝ) x - gt x)) =
      (fun x => M (endpointDerivative h (Fin n → ℝ) x) + g x) := by
    funext x
    rw [map_sub]
    change endpointDerivative h (Fin n → ℝ) x -
      (N (endpointDerivative h (Fin n → ℝ) x) - N (N.symm (g x))) = _
    rw [N.apply_symm_apply]
    have hn := congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L (endpointDerivative h (Fin n → ℝ) x)) hN
    change N (endpointDerivative h (Fin n → ℝ) x) =
      endpointDerivative h (Fin n → ℝ) x - M (endpointDerivative h (Fin n → ℝ) x) at hn
    rw [hn]
    abel
  rw [← heq]
  exact ⟨chart⟩

theorem terminal_atom_endpoint_coupling_of_isUnit
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (g : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hg : ContDiffOn ℝ 1 g U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U g)
    (M : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hM : IsUnit (1 - M)) :
    Nonempty (C1Straightening U (endpointDerivative h (Fin n → ℝ))
      (fun x => M (endpointDerivative h (Fin n → ℝ) x) + g x)) := by
  let N := ContinuousLinearEquiv.ofUnit hM.unit
  exact terminal_atom_endpoint_coupling h hh n U hU g hg hzero M N hM.unit_spec

end

end GlobalRegularization
