import GlobalRegularization.HistorySpace
import GlobalRegularization.ExtendedDerivative

/-!
# Concrete specification of the principal theorem

This file specifies the full localized existence claim on the actual
history spaces. `MainExistence.mainClaim` proves it. The older abstract
`MainTheoremTarget` is not used as a certificate for this claim.
-/

namespace GlobalRegularization

open scoped NNReal

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- All the spatial conclusions of the paper's principal theorem.
The common strict bound is stronger than a merely pointwise `< ε` bound. -/
structure LocalizedHistoryStraightening
    (U : Set (C1History h B)) (f : C1History h B → B) (τ ε : ℝ)
    extends C1Straightening U (endpointDerivative h B) f where
  preserves_zero : ∀ x ∈ U,
    historyInclusion h B (forward x) (historyRight h) =
      historyInclusion h B x (historyRight h)
  localized : ∀ x ∈ U, ∀ t : HistoryInterval h, (t : ℝ) ≤ -τ →
    historyInclusion h B (forward x) t = historyInclusion h B x t
  uniform_small : ∃ c : ℝ, c < ε ∧ ∀ x ∈ U,
    ‖historyInclusion h B (forward x - x)‖ ≤ c

/-- The requested principal existence claim. Its proof is `mainClaim`
in `MainExistence`; this definition itself introduces no axiom. -/
def MainClaim (n : ℕ) : Prop :=
  ∀ (h : ℝ≥0), 0 < (h : ℝ) →
  ∀ (U : Set (C1History h (Fin n → ℝ))) (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)),
    IsOpen U → HasExtendedDerivative U (historyInclusion h (Fin n → ℝ)) f →
    ∀ τ ε : ℝ, 0 < τ → τ < (h : ℝ) → 0 < ε →
      Nonempty (LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε)

end

end GlobalRegularization
