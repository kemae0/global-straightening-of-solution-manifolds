import GlobalRegularization.RevisedMainTheorems
import GlobalRegularization.PastDerivativeNonextension

/-! Literal strict local supremum bounds and the revised past-derivative
example's failure of property (e) on any open domain containing zero. -/

namespace GlobalRegularization

open Set Metric
open scoped NNReal

noncomputable section

theorem LocalC1Approximation.literal_sup_bound
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {U : Set E} {f : E → B} {fm : ℕ → E → B} (happ : LocalC1Approximation U f fm)
    {x : E} (hx : x ∈ U) (η : ℝ) (hη : 0 < η) :
    ∃ r > 0, ball x r ⊆ U ∧ ∃ N : ℕ,
      sSup ((fun p : ℕ × E => ‖fm p.1 p.2 - f p.2‖ +
        ‖fderiv ℝ (fm p.1) p.2 - fderiv ℝ f p.2‖) ''
          {p | N ≤ p.1 ∧ p.2 ∈ ball x r}) < η := by
  obtain ⟨r, hr, hball, N, c, hc, hbound⟩ := happ.uniform_margin hx η hη
  refine ⟨r, hr, hball, N, ?_⟩
  have hne : ({p : ℕ × E | N ≤ p.1 ∧ p.2 ∈ ball x r}).Nonempty :=
    ⟨(N, x), le_rfl, mem_ball_self hr⟩
  apply (csSup_le (hne.image _) ?_).trans_lt hc
  rintro a ⟨p, hp, rfl⟩
  exact hbound p.1 hp.1 p.2 hp.2

theorem scalarPastDerivativeFeedback_not_property_e_on_zero_domain
    (h : ℝ≥0) (t s : HistoryInterval h) (U : Set (C1History h ℝ)) (hzero : (0 : C1History h ℝ) ∈ U) :
    ¬ HasExtendedDerivative U (historyInclusion h ℝ) (scalarPastDerivativeFeedback h t s) := by
  intro he
  obtain ⟨F, hF, _⟩ := he.exists_extension
  exact scalarPastDerivativeFeedback_no_extended_derivative_at_zero h t s ⟨F 0, hF 0 hzero⟩

end

end GlobalRegularization
