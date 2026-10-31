import GlobalRegularization.FiniteFiltration

/-!
# Deriving the filtration from triangular observation identities

For `T = ∑ i < n, Qᵢ Aᵢ`, the one-sided identities `Aᵢ Qⱼ = 0`
when `i ≤ j` force `T^(n+1) = 0`. The filtration and its lowering
property are constructed here, rather than added as hypotheses.
-/

namespace GlobalRegularization

section

variable {R E B : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
  [AddCommMonoid B] [Module R B]

def finiteTriangle (Q : ℕ → B →ₗ[R] E) (A : ℕ → E →ₗ[R] B) (n : ℕ) :
    Module.End R E :=
  ∑ i ∈ Finset.range n, (Q i).comp (A i)

def triangularTailSpan (Q : ℕ → B →ₗ[R] E) (n k : ℕ) : Submodule R E :=
  Submodule.span R {x | ∃ j, j < n ∧ k ≤ j ∧ ∃ b, Q j b = x}

theorem finiteTriangle_range (Q : ℕ → B →ₗ[R] E) (A : ℕ → E →ₗ[R] B)
    (n : ℕ) (x : E) : finiteTriangle Q A n x ∈ triangularTailSpan Q n 0 := by
  simp only [finiteTriangle, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.subset_span ⟨j, Finset.mem_range.mp hj, Nat.zero_le j, A j x, rfl⟩

theorem finiteTriangle_lowers (Q : ℕ → B →ₗ[R] E) (A : ℕ → E →ₗ[R] B)
    (n : ℕ) (hann : ∀ i j, i < n → i ≤ j → (A i).comp (Q j) = 0)
    (k : ℕ) (x : E) (hx : x ∈ triangularTailSpan Q n k) :
    finiteTriangle Q A n x ∈ triangularTailSpan Q n (k + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, hjn, hkj, b, rfl⟩ := hx
      simp only [finiteTriangle, LinearMap.sum_apply, LinearMap.comp_apply]
      apply Submodule.sum_mem
      intro i hi
      by_cases hij : i ≤ j
      · have hzero : A i (Q j b) = 0 := by
          exact congrArg (fun L : B →ₗ[R] B => L b)
            (hann i j (Finset.mem_range.mp hi) hij)
        simp [hzero]
      · exact Submodule.subset_span
          ⟨i, Finset.mem_range.mp hi, by omega, A i (Q j b), rfl⟩
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using Submodule.add_mem _ hx' hy'
  | smul c x hx hx' => simpa only [map_smul] using Submodule.smul_mem _ c hx'

theorem triangularTailSpan_terminal (Q : ℕ → B →ₗ[R] E) (n : ℕ) :
    triangularTailSpan Q n n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨j, hj, hnj, b, hbx⟩
  omega

theorem finiteTriangle_pow_eq_zero (Q : ℕ → B →ₗ[R] E)
    (A : ℕ → E →ₗ[R] B) (n : ℕ)
    (hann : ∀ i j, i < n → i ≤ j → (A i).comp (Q j) = 0) :
    finiteTriangle Q A n ^ (n + 1) = 0 :=
  pow_eq_zero_of_range_filtration (finiteTriangle Q A n)
    (triangularTailSpan Q n) n (finiteTriangle_range Q A n)
    (triangularTailSpan_terminal Q n) (finiteTriangle_lowers Q A n hann)

end

end GlobalRegularization
