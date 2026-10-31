import GlobalRegularization.AdaptedHistoryOperators
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Separability of the genuine history space, not an assumed property of
an unrelated Banach model. -/

namespace GlobalRegularization

open Set Filter TopologicalSpace
open scoped NNReal Topology

instance (h : ℝ≥0) : SecondCountableTopology (HistoryInterval h) :=
  inferInstanceAs (SecondCountableTopology (Set.Icc (-(h : ℝ)) 0))

instance (h : ℝ≥0) (n : ℕ) : SecondCountableTopology (C1History h (Fin n → ℝ)) := by
  letI : SecondCountableTopology (ContinuousHistory h (Fin n → ℝ)) := inferInstance
  letI : SecondCountableTopology (ContinuousHistory h (Fin n → ℝ) × ContinuousHistory h (Fin n → ℝ)) := inferInstance
  change SecondCountableTopology ↥(LinearMap.ker (historyDefect h (Fin n → ℝ)))
  exact Subtype.secondCountableTopology (LinearMap.ker (historyDefect h (Fin n → ℝ)) :
    Set (ContinuousHistory h (Fin n → ℝ) × ContinuousHistory h (Fin n → ℝ)))

theorem history_derivative_image_separable (h : ℝ≥0) (n : ℕ)
    (U : Set (C1History h (Fin n → ℝ))) (hU : IsOpen U)
    (f : C1History h (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f U) :
    IsSeparable ((fderiv ℝ f) '' U) := by
  have hd : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hc : Continuous (fun x : U => fderiv ℝ f x) := hd.restrict
  have hs := (IsSeparable.of_separableSpace (univ : Set U)).image hc
  convert hs using 1
  ext L
  simp

end GlobalRegularization
