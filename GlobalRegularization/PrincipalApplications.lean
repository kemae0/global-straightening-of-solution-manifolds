import GlobalRegularization.MainExistence

/-! Unconditional compatibility-level consequences of the checked
principal theorem under property (e). -/

namespace GlobalRegularization

open Set
open scoped NNReal

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B]

theorem property_e_all_levels
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      ∀ b : B, chart.forward '' {x | x ∈ U ∧ endpointDerivative h B x - f x = b} =
        (chart.forward '' U) ∩ {y | endpointDerivative h B y = b} := by
  obtain ⟨chart⟩ := property_e_localized_straightening h B hh U hU f he τ ε hτ hε
  exact ⟨chart, fun b => c1_straightening_all_levels U (endpointDerivative h B) f chart.toC1Straightening b⟩

theorem property_e_solution_manifold
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      chart.forward '' solutionManifold U (endpointDerivative h B) f =
        (chart.forward '' U) ∩ zeroHyperplane (endpointDerivative h B) := by
  obtain ⟨chart⟩ := property_e_localized_straightening h B hh U hU f he τ ε hτ hε
  exact ⟨chart, c1_straightening_solution_manifold U (endpointDerivative h B) f chart.toC1Straightening⟩

end GlobalRegularization
