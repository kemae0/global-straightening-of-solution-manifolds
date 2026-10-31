import GlobalRegularization.HilbertCylindricalFamily
import GlobalRegularization.ApproximantStraightening

/-! The full normalized Hilbert-valued shell construction, using the
proved bounded Hilbert cylindrical approximants. -/

namespace GlobalRegularization

open Set Filter TopologicalSpace
open scoped NNReal Topology

noncomputable section

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]

theorem property_e_Hilbert_normalized_straightening
    (U : Set (C1History 1 H)) (hU : IsOpen U) (f : C1History 1 H → H)
    (he : HasExtendedDerivative U (historyInclusion 1 H) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening 1 H U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy ∧ chart.toC1Straightening.HasTriangularDerivative := by
  obtain ⟨fm, hsmooth, hbounded, happ, hfactor⟩ := property_e_Hilbert_bounded_C1_approximants H U hU f he
  apply localized_straightening_of_bounded_approximants 1 H U hU f he.c1 fm hsmooth hbounded happ
    (hilbertHistoryObservation H) hfactor (hilbertHistoryObservation_separates H)
    (fun n => 1 / (n + 1 : ℝ)) (fun n => by positivity) _
    (hilbertHistoryObservation_annihilates_terminal H) τ ε hτ hε
  intro m n hmn
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

end

end GlobalRegularization
