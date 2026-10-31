import GlobalRegularization.IntegralDensityFunctional
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Removing equal atoms from the two positive measures representing a
signed integral preserves the functional and gives atom-free components. -/

namespace GlobalRegularization

open Set MeasureTheory

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [MeasurableSingletonClass X]

def removeMeasureAtom (μ : Measure X) (a : X) : Measure X := μ.restrict ({a} : Set X)ᶜ

instance (μ : Measure X) [IsFiniteMeasure μ] (a : X) : IsFiniteMeasure (removeMeasureAtom μ a) :=
  inferInstanceAs (IsFiniteMeasure (μ.restrict ({a} : Set X)ᶜ))

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] in
theorem removeMeasureAtom_singleton (μ : Measure X) (a : X) : removeMeasureAtom μ a {a} = 0 := by
  simp [removeMeasureAtom, Measure.restrict_apply]

theorem integral_difference_remove_atom
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a : X)
    (hatom : μ.real {a} = ν.real {a}) (g : C(X, ℝ)) :
    (∫ t, g t ∂μ) - (∫ t, g t ∂ν) =
      (∫ t, g t ∂removeMeasureAtom μ a) - ∫ t, g t ∂removeMeasureAtom ν a := by
  have hμ := integral_add_compl (measurableSet_singleton a) (continuous_compact_integrable μ ℝ g)
  have hν := integral_add_compl (measurableSet_singleton a) (continuous_compact_integrable ν ℝ g)
  rw [integral_singleton, smul_eq_mul] at hμ hν
  change (∫ t, g t ∂μ) - (∫ t, g t ∂ν) = (∫ t in ({a} : Set X)ᶜ, g t ∂μ) - ∫ t in ({a} : Set X)ᶜ, g t ∂ν
  rw [← hμ, ← hν, hatom]
  ring

end

end GlobalRegularization
