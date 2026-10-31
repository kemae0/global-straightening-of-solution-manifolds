import GlobalRegularization.TerminalExistence

/-! All finite-state conclusions, including the spectrum of the actual
complexified derivative. Equality requires the nonzero state dimension;
the spectrum inclusion holds also in dimension zero. -/

namespace GlobalRegularization

open Set
open scoped NNReal

noncomputable section

theorem terminal_atom_full_straightening_spectrum_inclusion
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
        ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) ⊆ {1} := by
  obtain ⟨chart, hi, ht⟩ := terminal_atom_localized_straightening_with_triangular_derivative
    h hh n U hU f hf hzero τ ε hτ hε
  exact ⟨chart, hi, fun x hx => ht.spectrum_subset hx⟩

theorem terminal_atom_full_straightening
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ) [NeZero n]
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
        ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} := by
  letI : Nontrivial (C1History h (Fin n → ℝ)) :=
    Function.Injective.nontrivial (historyCoordinates h (Fin n → ℝ)).symm.injective
  obtain ⟨chart, hi, ht⟩ := terminal_atom_localized_straightening_with_triangular_derivative
    h hh n U hU f hf hzero τ ε hτ hε
  exact ⟨chart, hi, fun x hx => ht.spectrum_eq hx⟩

theorem property_e_full_straightening
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ) [NeZero n]
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ))
    (he : HasExtendedDerivative U (historyInclusion h (Fin n → ℝ)) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧
        ∀ x ∈ U, spectrum ℂ (RealComplexification.map (fderiv ℝ chart.forward x)) = {1} :=
  terminal_atom_full_straightening h hh n U hU f he.c1
    (fun _ hx δ hδ hlim => property_e_terminal_limit h (Fin n → ℝ) he δ hδ hlim hx) τ ε hτ hε

end

end GlobalRegularization
