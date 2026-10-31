import GlobalRegularization.VectorRieszRepresentation
import GlobalRegularization.HistoryTerminalAtom
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Operator-norm convergence to the matrix of endpoint atoms for an
arbitrary finite-dimensional history functional with its proved measure
representation. -/

namespace GlobalRegularization

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section

def realCoordinateVector (n : ℕ) (j : Fin n) : Fin n → ℝ := Pi.single j 1

theorem finiteCLM_basis_expansion (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    T = ∑ j : Fin n, (ContinuousLinearMap.proj j).smulRight (T (realCoordinateVector n j)) := by
  classical
  apply ContinuousLinearMap.ext
  intro a
  have ha : (∑ j : Fin n, a j • realCoordinateVector n j) = a := by
    ext k
    simp [realCoordinateVector, Pi.single_apply]
  calc
    T a = T (∑ j : Fin n, a j • realCoordinateVector n j) := congrArg T ha.symm
    _ = ∑ j : Fin n, a j • T (realCoordinateVector n j) := by simp only [map_sum, map_smul]
    _ = (∑ j : Fin n, (ContinuousLinearMap.proj j).smulRight (T (realCoordinateVector n j))) a := by
      simp

theorem finiteCLM_tendsto_of_entries (n : ℕ)
    (T : ℕ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hentry : ∀ i j, Tendsto (fun m => T m (realCoordinateVector n j) i) atTop
      (𝓝 (A (realCoordinateVector n j) i))) : Tendsto T atTop (𝓝 A) := by
  have hp (j : Fin n) : Tendsto (fun m => T m (realCoordinateVector n j)) atTop
      (𝓝 (A (realCoordinateVector n j))) := tendsto_pi_nhds.mpr (fun i => hentry i j)
  have hterm (j : Fin n) :=
    ((ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) (Fin n → ℝ) (ContinuousLinearMap.proj j)).continuous.tendsto
      (A (realCoordinateVector n j))).comp (hp j)
  have ht := tendsto_finset_sum Finset.univ (fun j hj => hterm j)
  have heval (j : Fin n) (v : Fin n → ℝ) :
      ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) (Fin n → ℝ) (ContinuousLinearMap.proj j) v =
        (ContinuousLinearMap.proj j).smulRight v := rfl
  change Tendsto (fun m => T m) atTop (𝓝 A)
  simpa only [Finset.sum_apply, Function.comp_apply, heval, ← finiteCLM_basis_expansion] using ht

def historyAtomOperator (h : ℝ≥0) (n : ℕ)
    (μ ν : Fin n → Fin n → Measure (HistoryInterval h)) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ∑ j : Fin n, (ContinuousLinearMap.proj j).smulRight
    (fun i => (μ i j).real {historyRight h} - (ν i j).real {historyRight h})

theorem historyAtomOperator_entry (h : ℝ≥0) (n : ℕ)
    (μ ν : Fin n → Fin n → Measure (HistoryInterval h)) (i j : Fin n) :
    historyAtomOperator h n μ ν (realCoordinateVector n j) i =
      (μ i j).real {historyRight h} - (ν i j).real {historyRight h} := by
  classical
  simp [historyAtomOperator, realCoordinateVector, Pi.single_apply, ite_apply]

theorem historyAtomOperator_eq_zero_iff (h : ℝ≥0) (n : ℕ)
    (μ ν : Fin n → Fin n → Measure (HistoryInterval h)) :
    historyAtomOperator h n μ ν = 0 ↔ ∀ i j,
      (μ i j).real {historyRight h} - (ν i j).real {historyRight h} = 0 := by
  classical
  constructor
  · intro hz i j
    have he := historyAtomOperator_entry h n μ ν i j
    rw [hz] at he
    exact he.symm
  · intro hz
    have hcol (j : Fin n) : (fun i => (μ i j).real {historyRight h} - (ν i j).real {historyRight h}) = 0 :=
      funext (fun i => hz i j)
    simp only [historyAtomOperator]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hcol]
    exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) (Fin n → ℝ) (ContinuousLinearMap.proj j)).map_zero

theorem matrixHistoryFunctional_terminal_operator_limit
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ ν : Fin n → Fin n → Measure (HistoryInterval h))
    [∀ i j, IsFiniteMeasure (μ i j)] [∀ i j, IsFiniteMeasure (ν i j)]
    (hrep : ∀ x i, L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
      ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
        ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ν i j))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m))) atTop
      (𝓝 (historyAtomOperator h n μ ν)) := by
  classical
  apply finiteCLM_tendsto_of_entries n
  intro i j
  rw [historyAtomOperator_entry]
  have hevent : ∀ᶠ m : ℕ in atTop, δ m < 2 * (h : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by positivity))
  have heq : (fun m => L (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m) (realCoordinateVector n j)) i)
      =ᶠ[atTop] (fun m =>
        (∫ t : HistoryInterval h, deriv (terminalProfile (δ m) (hδ m)) t ∂μ i j) -
          ∫ t : HistoryInterval h, deriv (terminalProfile (δ m) (hδ m)) t ∂ν i j) := by
    filter_upwards [hevent] with m hm
    have hleft : historyInclusion h (Fin n → ℝ)
        (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m) (realCoordinateVector n j)) (historyLeft h) = 0 := by
      apply terminalCorrection_localized
      change -(h : ℝ) ≤ -δ m / 2
      linarith
    have hder (t : HistoryInterval h) (k : Fin n) : historyDerivative h (Fin n → ℝ)
        (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m) (realCoordinateVector n j)) t k =
          if k = j then deriv (terminalProfile (δ m) (hδ m)) t else 0 := by
      change deriv (terminalProfile (δ m) (hδ m)) t * realCoordinateVector n j k = _
      simp [realCoordinateVector, Pi.single_apply]
    rw [hrep, hleft, map_zero, Pi.zero_apply, zero_add]
    have hterm (k : Fin n) :
        ((∫ t, historyDerivative h (Fin n → ℝ)
          (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m) (realCoordinateVector n j)) t k ∂μ i k) -
          ∫ t, historyDerivative h (Fin n → ℝ)
          (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m) (realCoordinateVector n j)) t k ∂ν i k) =
        if k = j then ((∫ t : HistoryInterval h, deriv (terminalProfile (δ m) (hδ m)) t ∂μ i j) -
          ∫ t : HistoryInterval h, deriv (terminalProfile (δ m) (hδ m)) t ∂ν i j) else 0 := by
      by_cases hk : k = j
      · subst k
        simp only [hder, if_true]
      · simp only [hder, if_neg hk, integral_zero, sub_self]
    simp_rw [hterm]
    simp
  apply (tendsto_congr' heq).mpr
  exact (integral_history_terminalProfile_deriv_tendsto_atom h (μ i j) δ hδ hlim).sub
    (integral_history_terminalProfile_deriv_tendsto_atom h (ν i j) δ hδ hlim)

theorem matrixHistoryFunctional_terminal_zero_iff
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ ν : Fin n → Fin n → Measure (HistoryInterval h))
    [∀ i j, IsFiniteMeasure (μ i j)] [∀ i j, IsFiniteMeasure (ν i j)]
    (hrep : ∀ x i, L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
      ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
        ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ν i j))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun m => L.comp (terminalCorrection h (Fin n → ℝ) (δ m) (hδ m))) atTop (𝓝 0) ↔
      ∀ i j, (μ i j).real {historyRight h} - (ν i j).real {historyRight h} = 0 := by
  have ht := matrixHistoryFunctional_terminal_operator_limit h hh n L A μ ν hrep δ hδ hlim
  constructor
  · intro hz
    exact (historyAtomOperator_eq_zero_iff h n μ ν).mp (tendsto_nhds_unique ht hz)
  · intro hz
    have he := (historyAtomOperator_eq_zero_iff h n μ ν).mpr hz
    simpa only [he] using ht

end

end GlobalRegularization
