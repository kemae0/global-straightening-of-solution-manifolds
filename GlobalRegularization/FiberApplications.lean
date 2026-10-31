import GlobalRegularization.TerminalExistence
import GlobalRegularization.SplitFibers

/-! The finite-state level-set corollary, with explicit global C¹ kernel
charts, a continuous complementary-plane family, and codimension n. -/

namespace GlobalRegularization

open Set
open scoped NNReal

noncomputable section

theorem terminal_atom_fiber_geometry
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U)
    (hzero : HasVanishingTerminalDerivative h (Fin n → ℝ) U f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h (Fin n → ℝ) U f τ ε,
      (∀ b : Fin n → ℝ, chart.forward '' {x | x ∈ U ∧ endpointDerivative h (Fin n → ℝ) x - f x = b} =
        (chart.forward '' U) ∩ {y | endpointDerivative h (Fin n → ℝ) y = b}) ∧
      (∀ b, Nonempty (SplitC1FiberParametrization U (endpointDerivative h (Fin n → ℝ)) f b)) ∧
      ∃ R : C1History h (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] C1History h (Fin n → ℝ),
        ContinuousOn R U ∧ ∀ x ∈ U,
          IsCompl (LinearMap.ker (fderiv ℝ (fun y => endpointDerivative h (Fin n → ℝ) y - f y) x))
            (LinearMap.range (R x)) ∧ Module.finrank ℝ (LinearMap.range (R x)) = n ∧
              Module.finrank ℝ (C1History h (Fin n → ℝ) ⧸
                LinearMap.ker (fderiv ℝ (fun y => endpointDerivative h (Fin n → ℝ) y - f y) x)) = n := by
  obtain ⟨chart⟩ := terminal_atom_localized_straightening h hh n U hU f hf hzero τ ε hτ hε
  let Q := terminalCorrection h (Fin n → ℝ) 1 zero_lt_one
  have hQ := terminalCorrection_endpoint h (Fin n → ℝ) 1 zero_lt_one
  have hc := chart.toC1Straightening.continuous_complement_family hU Q hQ
  refine ⟨chart, fun b => c1_straightening_all_levels U _ f chart.toC1Straightening b,
    fun b => ⟨chart.toC1Straightening.splitFiberParametrization Q hQ b⟩,
    chart.toC1Straightening.defectRightInverse Q, hc.1, ?_⟩
  intro x hx
  refine ⟨hc.2 x hx, ?_⟩
  simpa using chart.toC1Straightening.normal_dimension hU Q hQ hx

end

end GlobalRegularization
