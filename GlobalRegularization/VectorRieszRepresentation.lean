import GlobalRegularization.HistoryFunctionalRepresentation

/-! Componentwise finite-measure representation for finite-dimensional
continuous histories and for their endpoint/derivative functionals. -/

namespace GlobalRegularization

open Set MeasureTheory
open scoped NNReal

noncomputable section

variable {X : Type*} [TopologicalSpace X]

def continuousVectorInjection (n : ℕ) (j : Fin n) : C(X, ℝ) →L[ℝ] C(X, Fin n → ℝ) :=
  ContinuousLinearMap.compLeftContinuous ℝ X (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) j)

def continuousVectorComponent (n : ℕ) (j : Fin n) : C(X, Fin n → ℝ) →L[ℝ] C(X, ℝ) :=
  ContinuousLinearMap.compLeftContinuous ℝ X (ContinuousLinearMap.proj j)

@[simp]
theorem continuousVectorInjection_apply (n : ℕ) (j : Fin n) (g : C(X, ℝ)) (t : X) (k : Fin n) :
    continuousVectorInjection n j g t k = (Pi.single j (g t) : Fin n → ℝ) k := rfl

@[simp]
theorem continuousVectorComponent_apply (n : ℕ) (j : Fin n) (g : C(X, Fin n → ℝ)) (t : X) :
    continuousVectorComponent n j g t = g t j := rfl

theorem continuousVector_sum_components (n : ℕ) (g : C(X, Fin n → ℝ)) :
    (∑ j : Fin n, continuousVectorInjection n j (continuousVectorComponent n j g)) = g := by
  classical
  ext t k
  simp only [ContinuousMap.sum_apply, Finset.sum_apply, continuousVectorInjection_apply,
    continuousVectorComponent_apply, Pi.single_apply]
  simp

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]

theorem continuousVectorFunctional_representation (n : ℕ) (L : C(X, Fin n → ℝ) →L[ℝ] ℝ) :
    ∃ μ ν : Fin n → Measure X, (∀ j, IsFiniteMeasure (μ j)) ∧ (∀ j, IsFiniteMeasure (ν j)) ∧
      ∀ g : C(X, Fin n → ℝ), L g = ∑ j : Fin n,
        ((∫ t, g t j ∂μ j) - ∫ t, g t j ∂ν j) := by
  have hrep (j : Fin n) := continuousFunctional_riesz_difference (L.comp (continuousVectorInjection n j))
  choose μ ν hμ hν hrep using hrep
  refine ⟨μ, ν, hμ, hν, ?_⟩
  intro g
  calc
    L g = ∑ j : Fin n, L (continuousVectorInjection n j (continuousVectorComponent n j g)) := by
      rw [← map_sum, continuousVector_sum_components]
    _ = ∑ j : Fin n, ((∫ t, g t j ∂μ j) - ∫ t, g t j ∂ν j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hrep j (continuousVectorComponent n j g)

theorem historyFunctional_matrix_representation (h : ℝ≥0) (n : ℕ)
    (L : C1History h (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    ∃ A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
    ∃ μ ν : Fin n → Fin n → Measure (HistoryInterval h),
      (∀ i j, IsFiniteMeasure (μ i j)) ∧ (∀ i j, IsFiniteMeasure (ν i j)) ∧
      ∀ x i, L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i +
        ∑ j : Fin n, ((∫ t, historyDerivative h (Fin n → ℝ) x t j ∂μ i j) -
          ∫ t, historyDerivative h (Fin n → ℝ) x t j ∂ν i j) := by
  obtain ⟨A, D, hsplit⟩ := historyFunctional_split h (Fin n → ℝ) (Fin n → ℝ) L
  have hrep (i : Fin n) := continuousVectorFunctional_representation n ((ContinuousLinearMap.proj i).comp D)
  choose μ ν hμ hν hrep using hrep
  refine ⟨A, μ, ν, hμ, hν, ?_⟩
  intro x i
  have hx := congrArg (fun v : Fin n → ℝ => v i) (hsplit x)
  change L x i = A (historyInclusion h (Fin n → ℝ) x (historyLeft h)) i + D (historyDerivative h (Fin n → ℝ) x) i at hx
  rw [hx]
  congr 1
  exact hrep i (historyDerivative h (Fin n → ℝ) x)

end

end GlobalRegularization
