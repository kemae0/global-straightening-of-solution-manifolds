import GlobalRegularization.BernsteinRangeCutoffs
import GlobalRegularization.ApproximantStraightening

/-! Bounded C¹ approximants factoring through the paper's actual degree-4^m
Bernstein operators. This connects the literal observation construction to
the global Hilbert existence proof. -/

namespace GlobalRegularization

open Set Filter TopologicalSpace
open scoped Topology NNReal

noncomputable section

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]

theorem property_e_paperBernstein_bounded_C1_approximants
    (U : Set (C1History 1 H)) (hU : IsOpen U) (f : C1History 1 H → H)
    (he : HasExtendedDerivative U (historyInclusion 1 H) f) :
    ∃ fm : ℕ → C1History 1 H → H,
      (∀ n, ContDiff ℝ 1 (fm n)) ∧ (∀ n, Bornology.IsBounded (range (fm n))) ∧
      LocalC1Approximation U f fm ∧
      ∀ i x y, paperBernstein H i x = paperBernstein H i y → fm i x = fm i y := by
  obtain ⟨g, hg, hgb, happ, hfactor⟩ := property_e_Hilbert_bounded_C1_approximants H U hU f he
  refine ⟨fun m => g (paperBernsteinIndex m), fun m => hg _, fun m => hgb _, ?_, ?_⟩
  · intro x hx η hη
    obtain ⟨r, hr, hball, N, hN⟩ := happ x hx η hη
    exact ⟨r, hr, hball, N, fun m hm y hy => hN _ (hm.trans (paperBernsteinIndex_ge m)) y hy⟩
  · intro i x y hxy
    have hs := (unitHistoryBernstein_eq_iff_samples H (paperBernsteinIndex i) x y).mp hxy
    apply hfactor (paperBernsteinIndex i) x y
    exact congrArg (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (paperBernsteinIndex i + 2) => H)).symm hs

theorem paperBernstein_bounded_range_factors
    (m : ℕ) (g : C1History 1 H → H) (hg : ContDiff ℝ 1 g)
    (hgb : Bornology.IsBounded (range g))
    (hfactor : ∀ x y, paperBernstein H m x = paperBernstein H m y → g x = g y) :
    ∃ ghat : LinearMap.range (paperBernstein H m) → H,
      ContDiff ℝ 1 ghat ∧ Bornology.IsBounded (range ghat) ∧
      ∀ x, ghat ⟨paperBernstein H m x, ⟨x, rfl⟩⟩ = g x := by
  obtain ⟨q, hq⟩ := unitHistorySynthesis_has_left_inverse H (paperBernsteinIndex m)
  let R := (unitHistoryLagrangeSynthesis H (paperBernsteinIndex m)).comp
    (q.comp (LinearMap.range (paperBernstein H m)).subtypeL)
  have hRP (x : C1History 1 H) : paperBernstein H m (R ⟨paperBernstein H m x, ⟨x, rfl⟩⟩) = paperBernstein H m x := by
    have hsample := unitHistorySamples_right_inverse H (paperBernsteinIndex m)
    have hright (a : Fin (paperBernsteinIndex m + 2) → H) :
        unitHistorySamples H (paperBernsteinIndex m) (unitHistoryLagrangeSynthesis H (paperBernsteinIndex m) a) = a :=
      congrArg (fun L : (Fin (paperBernsteinIndex m + 2) → H) →L[ℝ] (Fin (paperBernsteinIndex m + 2) → H) => L a) hsample
    have hleft (a : Fin (paperBernsteinIndex m + 2) → H) :
        q (unitHistorySynthesis H (paperBernsteinIndex m) a) = a :=
      congrArg (fun L : (Fin (paperBernsteinIndex m + 2) → H) →L[ℝ] (Fin (paperBernsteinIndex m + 2) → H) => L a) hq
    change unitHistoryBernsteinCLM H (paperBernsteinIndex m)
      (unitHistoryLagrangeSynthesis H (paperBernsteinIndex m) (q (unitHistoryBernsteinCLM H (paperBernsteinIndex m) x))) = _
    rw [← unitHistorySynthesis_comp_samples]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hleft, hright]
    exact congrArg (fun L : C1History 1 H →L[ℝ] C1History 1 H => L x)
      (unitHistorySynthesis_comp_samples H (paperBernsteinIndex m))
  refine ⟨fun z => g (R z), hg.comp R.contDiff, hgb.subset ?_, ?_⟩
  · rintro y ⟨z, rfl⟩
    exact ⟨R z, rfl⟩
  · intro x
    exact hfactor _ x (hRP x)

end

end GlobalRegularization
