import GlobalRegularization.ManuscriptHilbertFamily
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
  obtain ⟨fm, hsmooth, hbounded, happ, hfactor⟩ := property_e_manuscript_Hilbert_family H U hU f he
  apply localized_straightening_of_bounded_approximants 1 H U hU f he.c1 fm hsmooth hbounded happ
    (fun n => paperBernstein H (n + 1)) hfactor
    (fun x y hxy => tendsto_nhds_unique
      (((paperBernstein_strong H x).comp (tendsto_add_atTop_nat 1)).congr hxy)
      ((paperBernstein_strong H y).comp (tendsto_add_atTop_nat 1)))
    (fun n => 1 / (4 : ℝ) ^ (n + 1)) (fun n => by positivity)
    (fun i j hij => paperBernstein_width_antitone (Nat.add_le_add_right hij 1))
    (fun n => paperBernstein_terminal_invisible H (n + 1)) τ ε hτ hε

end

end GlobalRegularization
