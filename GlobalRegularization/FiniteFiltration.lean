import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

/-!
# Finite filtration argument

This is the finite algebraic step in the coordinate lemma. It does not
assume nilpotence: it derives it from a lowering filtration.
-/

namespace GlobalRegularization

section Algebra

variable {R E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]

theorem pow_mem_filtration (T : Module.End R E) (F : ℕ → Submodule R E)
    (hstep : ∀ i x, x ∈ F i → T x ∈ F (i + 1))
    {i : ℕ} {x : E} (hx : x ∈ F i) (k : ℕ) :
    (T ^ k) x ∈ F (i + k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      simpa [pow_succ', Nat.add_assoc] using hstep (i + k) ((T ^ k) x) ih

theorem pow_eq_zero_of_filtration (T : Module.End R E)
    (F : ℕ → Submodule R E) (n : ℕ)
    (hstart : F 0 = ⊤) (hend : F n = ⊥)
    (hstep : ∀ i x, x ∈ F i → T x ∈ F (i + 1)) :
    T ^ n = 0 := by
  ext x
  have hx : x ∈ F 0 := by rw [hstart]; trivial
  have h := pow_mem_filtration T F hstep hx n
  simpa [hend] using h

theorem pow_eq_zero_of_range_filtration (T : Module.End R E)
    (F : ℕ → Submodule R E) (n : ℕ)
    (hstart : ∀ x, T x ∈ F 0) (hend : F n = ⊥)
    (hstep : ∀ i x, x ∈ F i → T x ∈ F (i + 1)) :
    T ^ (n + 1) = 0 := by
  ext x
  have h := pow_mem_filtration T F hstep (hstart x) n
  simpa [hend, pow_succ] using h

theorem isNilpotent_of_range_filtration (T : Module.End R E)
    (F : ℕ → Submodule R E) (n : ℕ)
    (hstart : ∀ x, T x ∈ F 0) (hend : F n = ⊥)
    (hstep : ∀ i x, x ∈ F i → T x ∈ F (i + 1)) :
    IsNilpotent T :=
  ⟨n + 1, pow_eq_zero_of_range_filtration T F n hstart hend hstep⟩

end Algebra

end GlobalRegularization
namespace GlobalRegularization

variable {X : Type*}

/-- Each iterate of a transformation belongs to the corresponding filtration
level, provided the first level is the whole space and every step descends one
level. -/
theorem iterate_mem_filtration
    (T : X → X) (F : ℕ → Set X)
    (hfirst : F 0 = Set.univ)
    (hstep : ∀ n : ℕ, ∀ x ∈ F n, T x ∈ F (n + 1))
    (n : ℕ) (x : X) :
    (T^[n]) x ∈ F n := by
  induction n with
  | zero =>
      simp [hfirst]
  | succ n ih =>
      have h := hstep n ((T^[n]) x) ih
      simpa only [Function.iterate_succ_apply'] using h

/-- Nilpotence follows whenever the finite filtration terminates at zero. -/
theorem iterate_eq_zero_of_filtration
    [Zero X] (T : X → X) (F : ℕ → Set X)
    (hfirst : F 0 = Set.univ)
    (hstep : ∀ n : ℕ, ∀ x ∈ F n, T x ∈ F (n + 1))
    (N : ℕ) (hterminal : F N = {0}) :
    ∀ x : X, (T^[N]) x = 0 := by
  intro x
  have hx := iterate_mem_filtration T F hfirst hstep N x
  simpa only [hterminal, Set.mem_singleton_iff] using hx

end GlobalRegularization

