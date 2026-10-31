import GlobalRegularization.TerminalExistence
import GlobalRegularization.FiniteFullTheorem

/-! The manuscript's remote-observation hypothesis implies the actual
terminal derivative limit, for arbitrary Banach observation spaces. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B Y : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def AnnihilatesTerminalSupport (L : C1History h B →L[ℝ] Y) (σ : ℝ) : Prop :=
  ∀ x, (∀ t : HistoryInterval h, (t : ℝ) < -σ → historyInclusion h B x t = 0) → L x = 0

theorem remote_observation_annihilates_terminal
    (L : C1History h B →L[ℝ] Y) (σ : ℝ)
    (hremote : AnnihilatesTerminalSupport h B Y L σ)
    (δ : ℝ) (hδ : 0 < δ) (hshort : δ / 2 < σ) :
    L.comp (terminalCorrection h B δ hδ) = 0 := by
  apply ContinuousLinearMap.ext
  intro a
  apply hremote
  intro t ht
  apply terminalCorrection_localized h B δ hδ a t
  linarith

theorem composition_terminal_condition_of_invisible
    (L : C1History h B →L[ℝ] Y) (σ : ℝ) (hσ : 0 < σ)
    (hinvisible : ∀ δ (hδ : 0 < δ), δ / 2 < σ → L.comp (terminalCorrection h B δ hδ) = 0)
    (W : Set (ContinuousHistory h B × Y)) (hW : IsOpen W)
    (G : ContinuousHistory h B × Y → B) (hG : ContDiffOn ℝ 1 G W) :
    ContDiffOn ℝ 1 (fun x => G (historyInclusion h B x, L x))
      ((historyInclusion h B).prod L ⁻¹' W) ∧
    HasVanishingTerminalDerivative h B ((historyInclusion h B).prod L ⁻¹' W)
      (fun x => G (historyInclusion h B x, L x)) := by
  let P := (historyInclusion h B).prod L
  refine ⟨hG.comp P.contDiff.contDiffOn (fun x hx => hx), ?_⟩
  intro x hx δ hδ hlim
  have hDG := (hG.contDiffAt (hW.mem_nhds hx)).differentiableAt le_rfl
  have hD : fderiv ℝ (fun x => G (historyInclusion h B x, L x)) x =
      (fderiv ℝ G (P x)).comp P :=
    (hDG.hasFDerivAt.comp x P.hasFDerivAt).fderiv
  let J := ContinuousLinearMap.inl ℝ (ContinuousHistory h B) Y
  have ht := ((ContinuousLinearMap.compL ℝ B (ContinuousHistory h B) B
    ((fderiv ℝ G (P x)).comp J)).continuous.tendsto 0).comp
      (terminalCorrection_tendsto_zero h B δ hδ hlim)
  simp only [map_zero] at ht
  have hsmall : ∀ᶠ m : ℕ in atTop, δ m < 2 * σ := hlim.eventually (Iio_mem_nhds (by positivity))
  apply ht.congr'
  filter_upwards [hsmall] with m hm
  rw [hD]
  have hz := hinvisible (δ m) (hδ m) (by linarith)
  have heq : P.comp (terminalCorrection h B (δ m) (hδ m)) =
      J.comp ((historyInclusion h B).comp (terminalCorrection h B (δ m) (hδ m))) := by
    apply ContinuousLinearMap.ext
    intro a
    have ha := congrArg (fun F : B →L[ℝ] Y => F a) hz
    change (historyInclusion h B (terminalCorrection h B (δ m) (hδ m) a),
      L (terminalCorrection h B (δ m) (hδ m) a)) = (_, 0)
    rw [show L (terminalCorrection h B (δ m) (hδ m) a) = 0 from ha]
    rfl
  change ((fderiv ℝ G (P x)).comp J).comp
    ((historyInclusion h B).comp (terminalCorrection h B (δ m) (hδ m))) = _
  rw [ContinuousLinearMap.comp_assoc, ← heq, ContinuousLinearMap.comp_assoc]

theorem remote_composition_terminal_condition
    (L : C1History h B →L[ℝ] Y) (σ : ℝ) (hσ : 0 < σ)
    (hremote : AnnihilatesTerminalSupport h B Y L σ)
    (W : Set (ContinuousHistory h B × Y)) (hW : IsOpen W)
    (G : ContinuousHistory h B × Y → B) (hG : ContDiffOn ℝ 1 G W) :
    ContDiffOn ℝ 1 (fun x => G (historyInclusion h B x, L x))
      ((historyInclusion h B).prod L ⁻¹' W) ∧
    HasVanishingTerminalDerivative h B ((historyInclusion h B).prod L ⁻¹' W)
      (fun x => G (historyInclusion h B x, L x)) :=
  composition_terminal_condition_of_invisible h B Y L σ hσ
    (fun δ hδ hshort => remote_observation_annihilates_terminal h B Y L σ hremote δ hδ hshort) W hW G hG

theorem remote_observation_localized_straightening
    (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] Y) (σ : ℝ) (hσ : 0 < σ)
    (hremote : AnnihilatesTerminalSupport h (Fin n → ℝ) Y L σ)
    (W : Set (ContinuousHistory h (Fin n → ℝ) × Y)) (hW : IsOpen W)
    (G : ContinuousHistory h (Fin n → ℝ) × Y → (Fin n → ℝ)) (hG : ContDiffOn ℝ 1 G W)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ)
      ((historyInclusion h (Fin n → ℝ)).prod L ⁻¹' W)
      (fun x => G (historyInclusion h (Fin n → ℝ) x, L x)) τ ε,
      chart.toC1Straightening.HasAffineIsotopy := by
  obtain ⟨hf, hzero⟩ := remote_composition_terminal_condition h (Fin n → ℝ) Y L σ hσ hremote W hW G hG
  exact terminal_atom_localized_straightening_with_isotopy h hh n _
    (hW.preimage ((historyInclusion h (Fin n → ℝ)).prod L).continuous) _ hf hzero τ ε hτ hε

theorem remote_observation_full_straightening
    (hh : 0 < (h : ℝ)) (n : ℕ) [NeZero n]
    (L : C1History h (Fin n → ℝ) →L[ℝ] Y) (σ : ℝ) (hσ : 0 < σ)
    (hremote : AnnihilatesTerminalSupport h (Fin n → ℝ) Y L σ)
    (W : Set (ContinuousHistory h (Fin n → ℝ) × Y)) (hW : IsOpen W)
    (G : ContinuousHistory h (Fin n → ℝ) × Y → (Fin n → ℝ)) (hG : ContDiffOn ℝ 1 G W)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ)
      ((historyInclusion h (Fin n → ℝ)).prod L ⁻¹' W)
      (fun x => G (historyInclusion h (Fin n → ℝ) x, L x)) τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
        ∀ x ∈ ((historyInclusion h (Fin n → ℝ)).prod L ⁻¹' W),
          spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  obtain ⟨hf, hzero⟩ := remote_composition_terminal_condition h (Fin n → ℝ) Y L σ hσ hremote W hW G hG
  exact terminal_atom_full_straightening h hh n _
    (hW.preimage ((historyInclusion h (Fin n → ℝ)).prod L).continuous) _ hf hzero τ ε hτ hε

end

end GlobalRegularization
