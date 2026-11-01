import GlobalRegularization.TerminalExistence

/-! The literal one-sided limit as a positive real terminal width tends
to zero, rather than just its sequence formulation. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped Topology NNReal

noncomputable section

def terminalCorrectionAtWidth (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B]
    [NormedSpace ℝ B] [CompleteSpace B] (δ : ℝ) : B →L[ℝ] C1History h B :=
  if hδ : 0 < δ then terminalCorrection h B δ hδ else 0

theorem matrixHistoryFunctional_terminal_filter_limit
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ ν : Fin n → Fin n → Measure (HistoryInterval h))
    [∀ i j, IsFiniteMeasure (μ i j)] [∀ i j, IsFiniteMeasure (ν i j)]
    (hrep : ∀ x i, L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
      ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
        ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ν i j)) :
    Tendsto (fun δ : ℝ => L.comp (terminalCorrectionAtWidth h (Fin n → ℝ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (historyAtomOperator h n μ ν)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro v hv
  have hpos : ∀ᶠ m in atTop, 0 < v m := hv.eventually self_mem_nhdsWithin
  have hv0 : Tendsto v atTop (𝓝 (0 : ℝ)) := hv.mono_right nhdsWithin_le_nhds
  let δ : ℕ → ℝ := fun m => if 0 < v m then v m else 1
  have hδ (m : ℕ) : 0 < δ m := by dsimp only [δ]; split_ifs with hm <;> positivity
  have heq : δ =ᶠ[atTop] v := hpos.mono (fun m hm => if_pos hm)
  have hlim : Tendsto δ atTop (𝓝 (0 : ℝ)) := (tendsto_congr' heq).mpr hv0
  have ht := matrixHistoryFunctional_terminal_operator_limit h hh n L A μ ν hrep δ hδ hlim
  apply (tendsto_congr' (show
    (fun m => L.comp (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m))) =ᶠ[atTop]
      ((fun δ : ℝ => L.comp (terminalCorrectionAtWidth h (Fin n → ℝ) δ)) ∘ v) from ?_)).mp ht
  filter_upwards [hpos] with m hm
  simp only [Function.comp_def, terminalCorrectionAtWidth, dif_pos hm, δ, if_pos hm]

theorem matrixHistoryFunctional_terminal_filter_zero_iff
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ ν : Fin n → Fin n → Measure (HistoryInterval h))
    [∀ i j, IsFiniteMeasure (μ i j)] [∀ i j, IsFiniteMeasure (ν i j)]
    (hrep : ∀ x i, L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
      ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
        ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ν i j)) :
    Tendsto (fun δ : ℝ => L.comp (terminalCorrectionAtWidth h (Fin n → ℝ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) ↔ ∀ i j, (μ i j).real {historyRight h} - (ν i j).real {historyRight h} = 0 := by
  have ht := matrixHistoryFunctional_terminal_filter_limit h hh n L A μ ν hrep
  rw [← historyAtomOperator_eq_zero_iff]
  constructor
  · intro hz
    exact tendsto_nhds_unique ht hz
  · intro hz
    simpa only [hz] using ht

end

end GlobalRegularization
