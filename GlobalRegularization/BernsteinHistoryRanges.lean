import GlobalRegularization.FiniteTensorCoefficients
import GlobalRegularization.BernsteinRealIndependence
import GlobalRegularization.HilbertHistoryObservations
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Normed.Operator.Banach

/-! Continuous coefficient inverses for the actual Bernstein histories,
surjectivity of nodal observations, and their actual range equivalence. -/

namespace GlobalRegularization

open Set Filter Polynomial
open scoped unitInterval NNReal Topology

noncomputable section

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem bernsteinSynthesis_has_left_inverse (n : ℕ) :
    ∃ q : C(I, B) →L[ℝ] (Fin (n + 1) → B),
      q.comp (bernsteinSynthesis B n) = ContinuousLinearMap.id ℝ (Fin (n + 1) → B) := by
  obtain ⟨q, hq⟩ := finite_tensor_coefficients (fun j : Fin (n + 1) => bernstein n j)
    (bernstein_real_independent n) B
  refine ⟨q, ?_⟩
  ext c k
  exact congrArg (fun a : Fin (n + 1) → B => a k) (hq c)

def unitIntervalHistoryPoint (t : I) : HistoryInterval 1 :=
  ⟨(t : ℝ) - 1, by
    change -(1 : ℝ) ≤ (t : ℝ) - 1 ∧ (t : ℝ) - 1 ≤ 0
    constructor <;> linarith [t.property.1, t.property.2]⟩

def unitHistoryUnshiftL : C1History 1 B →ₗ[ℝ] C(I, B) where
  toFun x := ⟨fun t => historyInclusion 1 B x (unitIntervalHistoryPoint t), by
    apply (historyInclusion 1 B x).continuous.comp
    exact (continuous_subtype_val.sub continuous_const).subtype_mk _⟩
  map_add' x y := by ext t; rfl
  map_smul' a x := by ext t; rfl

def unitHistoryUnshift : C1History 1 B →L[ℝ] C(I, B) :=
  (unitHistoryUnshiftL B).mkContinuous 1 (fun x => by
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
    intro t
    exact ((historyInclusion 1 B x).norm_coe_le_norm _).trans (le_max_left _ _))

theorem unitHistoryUnshift_synthesis (n : ℕ) (c : Fin (n + 2) → B) :
    unitHistoryUnshift B (unitHistorySynthesis B n c) = bernsteinSynthesis B (n + 1) c := by
  ext t
  change historyInclusion 1 B (unitHistorySynthesis B n c) (unitIntervalHistoryPoint t) = _
  rw [unitHistorySynthesis_value, bernsteinSynthesis_apply]
  have hshift : unitHistoryShift (unitIntervalHistoryPoint t) = t := by
    apply Subtype.ext
    change (t : ℝ) - 1 + 1 = (t : ℝ)
    ring
  rw [hshift]

theorem unitHistorySynthesis_has_left_inverse (n : ℕ) :
    ∃ q : C1History 1 B →L[ℝ] (Fin (n + 2) → B),
      q.comp (unitHistorySynthesis B n) = ContinuousLinearMap.id ℝ (Fin (n + 2) → B) := by
  obtain ⟨q, hq⟩ := bernsteinSynthesis_has_left_inverse B (n + 1)
  refine ⟨q.comp (unitHistoryUnshift B), ?_⟩
  ext c k
  have he := congrArg (fun L : (Fin (n + 2) → B) →L[ℝ] (Fin (n + 2) → B) => L c k) hq
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    unitHistoryUnshift_synthesis] using he

theorem unitHistoryNode_injective (n : ℕ) : Function.Injective (unitHistoryNode n) := by
  intro i j hij
  have h := congrArg (fun t : HistoryInterval 1 => (t : ℝ)) hij
  simp only [unitHistoryNode, bernstein.z, Nat.cast_add, Nat.cast_one] at h
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hdiv : (i : ℝ) / (n + 1 : ℝ) = (j : ℝ) / (n + 1 : ℝ) := by linarith
  have h' : (i : ℝ) = (j : ℝ) := (div_left_inj' hn).mp hdiv
  apply Fin.ext
  exact_mod_cast h'

def unitHistoryLagrange (n : ℕ) (j : Fin (n + 2)) : C1History 1 ℝ :=
  let p := Lagrange.basis Finset.univ (fun k : Fin (n + 2) => (unitHistoryNode n k : ℝ)) j
  historyOfC1Function 1 ℝ (fun t => p.eval t) (fun t => p.derivative.eval t)
    p.continuous p.derivative.continuous (fun t => p.hasDerivAt t)

theorem unitHistoryLagrange_at_node (n : ℕ) (j k : Fin (n + 2)) :
    historyInclusion 1 ℝ (unitHistoryLagrange n j) (unitHistoryNode n k) = if k = j then 1 else 0 := by
  classical
  change (Lagrange.basis Finset.univ (fun k : Fin (n + 2) => (unitHistoryNode n k : ℝ)) j).eval
    (unitHistoryNode n k : ℝ) = _
  by_cases hkj : k = j
  · subst k
    rw [if_pos rfl]
    exact Lagrange.eval_basis_self (s := Finset.univ)
      (v := fun k : Fin (n + 2) => (unitHistoryNode n k : ℝ)) (i := j)
      (Subtype.val_injective.comp (unitHistoryNode_injective n)).injOn (Finset.mem_univ _)
  · rw [if_neg hkj]
    exact Lagrange.eval_basis_of_ne (v := fun k : Fin (n + 2) => (unitHistoryNode n k : ℝ))
      (Ne.symm hkj) (Finset.mem_univ _)

theorem unitHistorySamples_surjective (n : ℕ) : Function.Surjective (unitHistorySamples B n) := by
  classical
  intro c
  refine ⟨∑ j : Fin (n + 2), scalarHistoryLift 1 B (unitHistoryLagrange n j) (c j), ?_⟩
  ext k
  simp only [unitHistorySamples_apply, map_sum, ContinuousMap.sum_apply,
    scalarHistoryLift_value, unitHistoryLagrange_at_node]
  simp

def unitHistoryLagrangeSynthesis (n : ℕ) : (Fin (n + 2) → B) →L[ℝ] C1History 1 B :=
  ∑ j : Fin (n + 2), (scalarHistoryLiftCLM 1 B (unitHistoryLagrange n j)).comp (ContinuousLinearMap.proj j)

theorem unitHistorySamples_right_inverse (n : ℕ) :
    (unitHistorySamples B n).comp (unitHistoryLagrangeSynthesis B n) =
      ContinuousLinearMap.id ℝ (Fin (n + 2) → B) := by
  classical
  ext c k
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, unitHistorySamples_apply,
    unitHistoryLagrangeSynthesis, ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply,
    map_sum, ContinuousMap.sum_apply]
  change (∑ j : Fin (n + 2), historyInclusion 1 B
    (scalarHistoryLift 1 B (unitHistoryLagrange n j) (c j)) (unitHistoryNode n k)) = c k
  simp only [scalarHistoryLift_value, unitHistoryLagrange_at_node]
  simp

theorem unitHistoryBernstein_range_eq_synthesis (n : ℕ) :
    LinearMap.range (unitHistoryBernsteinCLM B n) = LinearMap.range (unitHistorySynthesis B n) := by
  rw [← unitHistorySynthesis_comp_samples]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (unitHistorySamples_surjective B n))

theorem unitHistorySynthesis_injective (n : ℕ) : Function.Injective (unitHistorySynthesis B n) := by
  obtain ⟨q, hq⟩ := unitHistorySynthesis_has_left_inverse B n
  have hl : Function.LeftInverse q (unitHistorySynthesis B n) := fun c =>
    congrArg (fun L : (Fin (n + 2) → B) →L[ℝ] (Fin (n + 2) → B) => L c) hq
  exact hl.injective

theorem unitHistorySynthesis_range_closed (n : ℕ) : IsClosed (range (unitHistorySynthesis B n)) := by
  obtain ⟨q, hq⟩ := unitHistorySynthesis_has_left_inverse B n
  have hl (c : Fin (n + 2) → B) : q (unitHistorySynthesis B n c) = c :=
    congrArg (fun L : (Fin (n + 2) → B) →L[ℝ] (Fin (n + 2) → B) => L c) hq
  have he : range (unitHistorySynthesis B n) = {x | unitHistorySynthesis B n (q x) = x} := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact congrArg (unitHistorySynthesis B n) (hl c)
    · intro hx
      exact ⟨q x, hx⟩
  rw [he]
  exact isClosed_eq ((unitHistorySynthesis B n).continuous.comp q.continuous) continuous_id

def unitHistorySynthesisRangeEquiv (n : ℕ) :
    (Fin (n + 2) → B) ≃L[ℝ] LinearMap.range (unitHistorySynthesis B n) :=
  (unitHistorySynthesis B n).equivRange (unitHistorySynthesis_injective B n)
    (unitHistorySynthesis_range_closed B n)

theorem unitHistoryBernstein_eq_iff_samples (n : ℕ) (x y : C1History 1 B) :
    unitHistoryBernsteinCLM B n x = unitHistoryBernsteinCLM B n y ↔
      unitHistorySamples B n x = unitHistorySamples B n y := by
  constructor
  · intro hxy
    apply unitHistorySynthesis_injective B n
    simpa only [← ContinuousLinearMap.comp_apply, unitHistorySynthesis_comp_samples] using hxy
  · exact unitHistoryBernstein_factors B n

def hilbertBernsteinRangeEquiv (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (n : ℕ) :
    HilbertHistoryObservationSpace H n ≃L[ℝ] LinearMap.range (unitHistoryBernsteinCLM H n) := by
  rw [unitHistoryBernstein_range_eq_synthesis]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 2) => H)).trans
    (unitHistorySynthesisRangeEquiv H n)

end

end GlobalRegularization
