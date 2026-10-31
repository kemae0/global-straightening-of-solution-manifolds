import GlobalRegularization.UnitHistoryApproximation
import GlobalRegularization.BoundaryLayer
import Mathlib.LinearAlgebra.Isomorphisms

/-! Finite nodal observations for the actual history approximants.
Finite rank and invisibility of sufficiently short terminal corrections
are proved, including the endpoint grid point where the value is zero. -/

namespace GlobalRegularization

open scoped unitInterval NNReal

noncomputable section

def unitHistoryNode (n : ℕ) (k : Fin (n + 2)) : HistoryInterval 1 :=
  ⟨(bernstein.z (n := n + 1) k : ℝ) - 1, by
    have hz := (bernstein.z (n := n + 1) k).property
    change -(1 : ℝ) ≤ _ ∧ _ ≤ 0
    constructor <;> linarith [hz.1, hz.2]⟩

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def unitHistorySamples (n : ℕ) : C1History 1 B →L[ℝ] (Fin (n + 2) → B) :=
  ContinuousLinearMap.pi (fun k =>
    (ContinuousMap.evalCLM ℝ (unitHistoryNode n k)).comp (historyInclusion 1 B))

@[simp]
theorem unitHistorySamples_apply (n : ℕ) (x : C1History 1 B) (k : Fin (n + 2)) :
    unitHistorySamples B n x k = historyInclusion 1 B x (unitHistoryNode n k) := rfl

theorem unitHistoryGlobalValue_at_node (n : ℕ) (x : C1History 1 B) (k : Fin (n + 2)) :
    bernsteinCurveSamples (unitHistoryGlobalValue B x) n k =
      historyInclusion 1 B x (unitHistoryNode n k) := by
  simpa only [bernsteinCurveSamples, unitHistoryGlobalValue, unitHistoryNode,
    bernstein.z, Nat.cast_add, Nat.cast_one] using
      differentiableHistoryExtension_coe 1 B x (unitHistoryNode n k)

theorem unitHistoryBernstein_observation_formula (n : ℕ) (x : C1History 1 B)
    (t : HistoryInterval 1) :
    historyInclusion 1 B (unitHistoryBernstein B n x) t =
      ∑ k : Fin (n + 2), bernstein (n + 1) k (unitHistoryShift t) • unitHistorySamples B n x k := by
  have heq := congrArg (fun F : C(I, B) => F (unitHistoryShift t))
    (bernsteinCurveCM_eq_synthesis (n + 1) (bernsteinCurveSamples (unitHistoryGlobalValue B x) n))
  simpa only [bernsteinSynthesis_apply, unitHistoryGlobalValue_at_node, unitHistorySamples_apply] using heq

theorem unitHistoryBernstein_factors (n : ℕ) {x y : C1History 1 B}
    (hobs : unitHistorySamples B n x = unitHistorySamples B n y) :
    unitHistoryBernstein B n x = unitHistoryBernstein B n y := by
  apply historyInclusion_injective 1 B (by norm_num)
  ext t
  rw [unitHistoryBernstein_observation_formula, unitHistoryBernstein_observation_formula, hobs]

theorem unitHistoryBernstein_finite_range [FiniteDimensional ℝ B] (n : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (unitHistoryBernsteinCLM B n)) := by
  let O := (unitHistorySamples B n).toLinearMap
  let T := (unitHistoryBernsteinCLM B n).toLinearMap
  have hk : LinearMap.ker O ≤ LinearMap.ker T := by
    intro x hx
    have hobs : unitHistorySamples B n x = unitHistorySamples B n 0 := by simpa using hx
    have hP := unitHistoryBernstein_factors B n hobs
    change T x = T 0 at hP
    simpa only [LinearMap.mem_ker, map_zero] using hP
  letI : FiniteDimensional ℝ (C1History 1 B ⧸ LinearMap.ker O) :=
    FiniteDimensional.of_injective O.quotKerEquivRange.toLinearMap O.quotKerEquivRange.injective
  have hr := Submodule.range_liftQ (LinearMap.ker O) T hk
  change FiniteDimensional ℝ (LinearMap.range T)
  rw [← hr]
  infer_instance

theorem unitHistorySamples_annihilate_terminal (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hshort : δ / 2 < 1 / (n + 1 : ℝ)) :
    (unitHistorySamples B n).comp (terminalCorrection 1 B δ hδ) = 0 := by
  ext a k
  change historyInclusion 1 B (terminalCorrection 1 B δ hδ a) (unitHistoryNode n k) = 0
  by_cases hk : (k : ℕ) = n + 1
  · have hnode : unitHistoryNode n k = historyRight 1 := by
      apply Subtype.ext
      simp [unitHistoryNode, bernstein.z, hk, historyRight]
      field_simp; norm_num
    rw [hnode]
    exact terminalCorrection_value_zero 1 B δ hδ a
  · have hkn : (k : ℕ) ≤ n := by omega
    have hnR : 0 < (n + 1 : ℝ) := by positivity
    have hkr : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hrat := div_le_div_of_nonneg_right hkr hnR.le
    have hid : (n : ℝ) / (n + 1 : ℝ) - 1 = -(1 / (n + 1 : ℝ)) := by field_simp; ring
    have hnodeval : (unitHistoryNode n k : ℝ) = (k : ℝ) / (n + 1 : ℝ) - 1 := by
      simp only [unitHistoryNode, bernstein.z, Nat.cast_add, Nat.cast_one]
    have hneg : (unitHistoryNode n k : ℝ) ≤ -δ / 2 := by rw [hnodeval]; linarith
    exact terminalCorrection_localized 1 B δ hδ a (unitHistoryNode n k) hneg

theorem unitHistoryBernstein_annihilates_terminal (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hshort : δ / 2 < 1 / (n + 1 : ℝ)) :
    (unitHistoryBernsteinCLM B n).comp (terminalCorrection 1 B δ hδ) = 0 := by
  ext a
  have hobs := congrArg (fun O : B →L[ℝ] (Fin (n + 2) → B) => O a)
    (unitHistorySamples_annihilate_terminal B n δ hδ hshort)
  have hobs' : unitHistorySamples B n (terminalCorrection 1 B δ hδ a) = unitHistorySamples B n 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero] using hobs
  have hP := unitHistoryBernstein_factors B n hobs'
  change (unitHistoryBernsteinCLM B n) (terminalCorrection 1 B δ hδ a) =
    (unitHistoryBernsteinCLM B n) 0 at hP
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero] using hP

end

end GlobalRegularization
