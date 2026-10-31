import GlobalRegularization.UnitHistoryObservations
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Hilbert observation ranges and actual Bernstein reconstruction.
Finite products carry their genuine Hilbert norm, and the reconstructed
operator is exactly the already checked history Bernstein approximation. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

def scalarBernsteinHistory (n : ℕ) (k : Fin (n + 2)) : C1History 1 ℝ :=
  historyOfC1Function 1 ℝ
    (fun t => (bernsteinPolynomial ℝ (n + 1) k).eval (t + 1))
    (fun t => (bernsteinPolynomial ℝ (n + 1) k).derivative.eval (t + 1))
    ((bernsteinPolynomial ℝ (n + 1) k).continuous.comp (continuous_id.add continuous_const))
    ((bernsteinPolynomial ℝ (n + 1) k).derivative.continuous.comp (continuous_id.add continuous_const))
    (fun t => by
      simpa only [Function.comp_def, one_smul] using
        ((bernsteinPolynomial ℝ (n + 1) k).hasDerivAt (t + 1)).scomp t ((hasDerivAt_id t).add_const 1))

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def unitHistorySynthesis (n : ℕ) : (Fin (n + 2) → B) →L[ℝ] C1History 1 B :=
  ∑ k : Fin (n + 2), (scalarHistoryLiftCLM 1 B (scalarBernsteinHistory n k)).comp (ContinuousLinearMap.proj k)

theorem unitHistorySynthesis_value (n : ℕ) (c : Fin (n + 2) → B) (t : HistoryInterval 1) :
    historyInclusion 1 B (unitHistorySynthesis B n c) t =
      ∑ k : Fin (n + 2), bernstein (n + 1) k (unitHistoryShift t) • c k := by
  simp only [unitHistorySynthesis, ContinuousLinearMap.sum_apply, map_sum, ContinuousMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

theorem unitHistorySynthesis_comp_samples (n : ℕ) :
    (unitHistorySynthesis B n).comp (unitHistorySamples B n) = unitHistoryBernsteinCLM B n := by
  apply ContinuousLinearMap.ext
  intro x
  apply historyInclusion_injective 1 B (by norm_num)
  ext t
  rw [ContinuousLinearMap.comp_apply, unitHistorySynthesis_value]
  exact (unitHistoryBernstein_observation_formula B n x t).symm

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev HilbertHistoryObservationSpace (n : ℕ) := PiLp 2 (fun _ : Fin (n + 2) => H)

def hilbertHistoryObservation (n : ℕ) : C1History 1 H →L[ℝ] HilbertHistoryObservationSpace H n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 2) => H)).symm.toContinuousLinearMap.comp
    (unitHistorySamples H n)

def hilbertHistoryReconstruction (n : ℕ) : HilbertHistoryObservationSpace H n →L[ℝ] C1History 1 H :=
  (unitHistorySynthesis H n).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 2) => H)).toContinuousLinearMap

theorem hilbertHistory_reconstruction_observation (n : ℕ) :
    (hilbertHistoryReconstruction H n).comp (hilbertHistoryObservation H n) = unitHistoryBernsteinCLM H n := by
  ext x
  change unitHistorySynthesis H n
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 2) => H))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 2) => H)).symm (unitHistorySamples H n x))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (fun T : C1History 1 H →L[ℝ] C1History 1 H => T x) (unitHistorySynthesis_comp_samples H n)

theorem hilbertHistoryObservation_annihilates_terminal (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hshort : δ / 2 < 1 / (n + 1 : ℝ)) :
    (hilbertHistoryObservation H n).comp (terminalCorrection 1 H δ hδ) = 0 := by
  rw [hilbertHistoryObservation, ContinuousLinearMap.comp_assoc,
    unitHistorySamples_annihilate_terminal H n δ hδ hshort, ContinuousLinearMap.comp_zero]

theorem hilbertHistoryObservation_separates (x y : C1History 1 H)
    (hobs : ∀ n, hilbertHistoryObservation H n x = hilbertHistoryObservation H n y) : x = y := by
  have hP (n : ℕ) : unitHistoryBernsteinCLM H n x = unitHistoryBernsteinCLM H n y := by
    have he := congrArg (hilbertHistoryReconstruction H n) (hobs n)
    simpa only [← ContinuousLinearMap.comp_apply, hilbertHistory_reconstruction_observation] using he
  have hP' (n : ℕ) : unitHistoryBernstein H n x = unitHistoryBernstein H n y := hP n
  exact tendsto_nhds_unique (unitHistoryBernstein_strong H x)
    ((tendsto_congr hP').mpr (unitHistoryBernstein_strong H y))

end

end GlobalRegularization
