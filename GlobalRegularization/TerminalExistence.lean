import GlobalRegularization.SeparableAdaptedOperators
import GlobalRegularization.AdaptedStraightening

/-! The stronger finite-state terminal-atom theorem, on the genuine history
space and arbitrary open domains, including the empty domain. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

/-- The sequential form of the limit as the positive terminal width tends
to zero. The matrix representation theorem identifies this with a zero
endpoint atom; property (e) is not assumed. -/
def HasVanishingTerminalDerivative (h : ℝ≥0) (B : Type*)
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (U : Set (C1History h B)) (f : C1History h B → B) : Prop :=
  ∀ x ∈ U, ∀ (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m), Tendsto δ atTop (𝓝 0) →
    Tendsto (fun m => (fderiv ℝ f x).comp (terminalCorrection h B (δ m) (hδ m))) atTop (𝓝 0)

theorem historyFunctional_terminal_sequences_iff
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (∀ (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m), Tendsto δ atTop (𝓝 0) →
      Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m))) atTop (𝓝 0)) ↔
    Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ)
      (adaptedTerminalWidth h m) (adaptedTerminalWidth_pos h hh m))) atTop (𝓝 0) := by
  constructor
  · intro hL
    exact hL _ _ (adaptedTerminalWidth_tendsto h)
  · intro hL
    obtain ⟨A, μ, ν, hμ, hν, hμatom, hνatom, hrep⟩ := historyFunctional_atomfree_representation h hh n L hL
    letI := hμ
    letI := hν
    intro δ hδ hlim
    apply (matrixHistoryFunctional_terminal_zero_iff h hh n L A μ ν hrep δ hδ hlim).mpr
    intro i j
    simp only [MeasureTheory.measureReal_def, hμatom, hνatom, ENNReal.toReal_zero, sub_self]

theorem terminal_atom_localized_straightening_with_triangular_derivative
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧ chart.toC1Straightening.HasTriangularDerivative := by
  have hsep := history_derivative_image_separable h n U hU f hf
  have hfixed : ∀ L ∈ (fderiv ℝ f) '' U, Tendsto (fun m => L.comp
      (terminalCorrection h (Fin n → ℝ) (adaptedTerminalWidth h m)
        (adaptedTerminalWidth_pos h hh m))) atTop (𝓝 0) := by
    rintro L ⟨x, hx, rfl⟩
    exact hzero x hx _ _ (adaptedTerminalWidth_tendsto h)
  obtain ⟨P, C, hC, hP, hstrong, hfinite, hadjoint, hinvisible⟩ :=
    exists_adapted_operators_for_separable_family h hh n _ hsep hfixed
  apply localized_straightening_of_adapted_operators_with_triangular_derivative h (Fin n → ℝ) U hU f hf
    P C hC hP hstrong hfinite _ (adaptedTerminalWidth h) (adaptedTerminalWidth_pos h hh)
    (adaptedTerminalWidth_antitone h) hinvisible τ ε hτ hε
  intro x hx
  exact hadjoint _ ⟨x, hx, rfl⟩

theorem terminal_atom_localized_straightening_with_isotopy
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy := by
  obtain ⟨chart, hi, ht⟩ := terminal_atom_localized_straightening_with_triangular_derivative
    h hh n U hU f hf hzero τ ε hτ hε
  exact ⟨chart, hi⟩

theorem terminal_atom_localized_straightening
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    Nonempty (LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε) := by
  obtain ⟨chart, hisotopy⟩ := terminal_atom_localized_straightening_with_isotopy h hh n U hU f hf hzero τ ε hτ hε
  exact ⟨chart⟩

end

end GlobalRegularization
