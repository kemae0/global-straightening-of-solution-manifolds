import Mathlib.Tactic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Minimal obstruction beyond the extended-derivative hypothesis

This is the one-dimensional exact-defect obstruction: if `D=f=id`, then
any map satisfying `D ∘ A = D-f` must be constant, hence cannot be an
ambient coordinate change. The proof is purely algebraic and is not a
formalization of the analytic main theorem.


-/

namespace GlobalRegularization

/-- The compatibility-defect identity for `D = f = id` forces the
coordinate map to be constantly zero. -/
theorem endpoint_identity_forces_constant
    (A : ℝ → ℝ) (hA : ∀ x : ℝ, A x = x - x) :
    ∀ x : ℝ, A x = 0 := by
  intro x
  simpa using hA x

/-- Consequently no injective exact straightening exists for this
functional, even on the entire one-dimensional phase space. -/
theorem no_injective_straightening_for_identity :
    ¬ ∃ A : ℝ → ℝ, Function.Injective A ∧
      (∀ x : ℝ, A x = x - x) := by
  rintro ⟨A, hInjective, hDefect⟩
  have hZero : A 0 = 0 := endpoint_identity_forces_constant A hDefect 0
  have hOne : A 1 = 0 := endpoint_identity_forces_constant A hDefect 1
  have h01 : (0 : ℝ) = 1 := hInjective (hZero.trans hOne.symm)
  norm_num at h01

/-- The spectrum-equals-`{1}` clauses in the coordinate and Hilbert
lemmas require a nontrivial state space. In the zero space it is empty. -/
theorem zero_space_identity_spectrum :
    spectrum ℂ (1 : (Fin 0 → ℂ) →L[ℂ] (Fin 0 → ℂ)) = ∅ :=
  spectrum.of_subsingleton _

theorem zero_space_identity_spectrum_ne_one :
    spectrum ℂ (1 : (Fin 0 → ℂ) →L[ℂ] (Fin 0 → ℂ)) ≠ {1} := by
  rw [zero_space_identity_spectrum]
  intro heq
  have hm : (1 : ℂ) ∈ (∅ : Set ℂ) := heq.symm ▸ (Set.mem_singleton_iff.mpr rfl)
  exact hm

end GlobalRegularization
