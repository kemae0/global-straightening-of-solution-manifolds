import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Tactic

/-! A real continuous functional on continuous functions is a difference
of positive linear functionals. The positive extension is constructed
using the M. Riesz extension theorem on two copies of the function space. -/

namespace GlobalRegularization

open Set

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

def doubledEmbedding : (C(X, ℝ) × ℝ) →ₗ[ℝ] (C(X, ℝ) × C(X, ℝ)) where
  toFun z := (z.1 + ContinuousMap.const X z.2, -z.1 + ContinuousMap.const X z.2)
  map_add' z w := by
    apply Prod.ext <;> ext x <;> simp only [Prod.fst_add, Prod.snd_add, ContinuousMap.add_apply,
      ContinuousMap.const_apply, ContinuousMap.neg_apply] <;> ring
  map_smul' c z := by
    apply Prod.ext
    · ext x
      change c * z.1 x + c * z.2 = c * (z.1 x + z.2)
      ring
    · ext x
      change -(c * z.1 x) + c * z.2 = c * (-z.1 x + z.2)
      ring

def doubledFunctional (L : C(X, ℝ) →L[ℝ] ℝ) (x₀ : X) :
    (C(X, ℝ) × C(X, ℝ)) →L[ℝ] ℝ :=
  L.comp ((1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _)) +
    (‖L‖ / 2 : ℝ) • (ContinuousMap.evalCLM ℝ x₀).comp
      (ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _)

omit [Nonempty X] in
theorem doubledFunctional_embedding (L : C(X, ℝ) →L[ℝ] ℝ) (x₀ : X) (f : C(X, ℝ)) (t : ℝ) :
    doubledFunctional L x₀ (doubledEmbedding (f, t)) = L f + ‖L‖ * t := by
  have hf : (1 / 2 : ℝ) • ((f + ContinuousMap.const X t) - (-f + ContinuousMap.const X t)) = f := by
    ext x
    simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.const_apply, ContinuousMap.neg_apply, smul_eq_mul]
    ring
  change L ((1 / 2 : ℝ) • ((f + ContinuousMap.const X t) - (-f + ContinuousMap.const X t))) +
    ‖L‖ / 2 * ((f x₀ + t) + (-f x₀ + t)) = _
  rw [hf]
  ring

theorem exists_positive_functional_decomposition_bounded (L : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ P N : C(X, ℝ) →ₚ[ℝ] ℝ, (∀ f, L f = P f - N f) ∧ P 1 + N 1 = ‖L‖ := by
  let x₀ : X := Classical.arbitrary X
  let I : (C(X, ℝ) × ℝ) →ₗ[ℝ] (C(X, ℝ) × C(X, ℝ)) := doubledEmbedding
  let p := LinearMap.range I
  let F : (C(X, ℝ) × C(X, ℝ)) →ₗ.[ℝ] ℝ :=
    ⟨p, (doubledFunctional L x₀).toLinearMap.comp p.subtype⟩
  let cone : ConvexCone ℝ (C(X, ℝ) × C(X, ℝ)) :=
    { carrier := {y | 0 ≤ y}
      smul_mem' := by
        intro c hc y hy
        constructor
        · intro x
          exact mul_nonneg hc.le (hy.1 x)
        · intro x
          exact mul_nonneg hc.le (hy.2 x)
      add_mem' := by
        intro y hy z hz
        constructor
        · intro x
          exact add_nonneg (hy.1 x) (hz.1 x)
        · intro x
          exact add_nonneg (hy.2 x) (hz.2 x) }
  have hnonneg : ∀ z : F.domain, (z : C(X, ℝ) × C(X, ℝ)) ∈ cone → 0 ≤ F z := by
    intro z hz
    obtain ⟨⟨f, t⟩, heq⟩ := z.property
    have hpos : 0 ≤ I (f, t) := by rw [heq]; exact hz
    have ht : 0 ≤ t := by
      have h₁ := hpos.1 x₀
      have h₂ := hpos.2 x₀
      change 0 ≤ f x₀ + t at h₁
      change 0 ≤ -f x₀ + t at h₂
      linarith
    have hnorm : ‖f‖ ≤ t := by
      apply (ContinuousMap.norm_le f ht).2
      intro x
      have h₁ := hpos.1 x
      have h₂ := hpos.2 x
      change 0 ≤ f x + t at h₁
      change 0 ≤ -f x + t at h₂
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hL := (abs_le.mp (L.le_opNorm f)).1
    have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg L)
    change 0 ≤ doubledFunctional L x₀ z.val
    rw [← heq, doubledFunctional_embedding]
    linarith
  have hdense : ∀ y, ∃ z : F.domain, (z : C(X, ℝ) × C(X, ℝ)) + y ∈ cone := by
    intro y
    refine ⟨⟨I (0, ‖y‖), ⟨(0, ‖y‖), rfl⟩⟩, ?_⟩
    change 0 ≤ I (0, ‖y‖) + y
    constructor
    · intro x
      have hx := (abs_le.mp (y.1.norm_coe_le_norm x)).1
      have hn : ‖y.1‖ ≤ ‖y‖ := le_max_left _ _
      change 0 ≤ 0 + ‖y‖ + y.1 x
      linarith
    · intro x
      have hx := (abs_le.mp (y.2.norm_coe_le_norm x)).1
      have hn : ‖y.2‖ ≤ ‖y‖ := le_max_right _ _
      change 0 ≤ -0 + ‖y‖ + y.2 x
      linarith
  obtain ⟨G, hagree, hpositive⟩ := riesz_extension cone F hnonneg hdense
  have hmono : Monotone G := by
    intro z w hzw
    have hdiff : w - z ∈ cone := by
      constructor
      · intro x
        exact sub_nonneg.mpr (hzw.1 x)
      · intro x
        exact sub_nonneg.mpr (hzw.2 x)
    have hp := hpositive (w - z) hdiff
    rw [map_sub] at hp
    exact sub_nonneg.mp hp
  let P : C(X, ℝ) →ₚ[ℝ] ℝ :=
    ⟨G.comp (LinearMap.inl ℝ _ _), fun f g hfg => hmono ⟨hfg, le_rfl⟩⟩
  let N : C(X, ℝ) →ₚ[ℝ] ℝ :=
    ⟨G.comp (LinearMap.inr ℝ _ _), fun f g hfg => hmono ⟨le_rfl, hfg⟩⟩
  refine ⟨P, N, ?_, ?_⟩
  · intro f
    have he := hagree ⟨I (f, 0), ⟨(f, 0), rfl⟩⟩
    change G (I (f, 0)) = doubledFunctional L x₀ (I (f, 0)) at he
    rw [doubledFunctional_embedding, mul_zero, add_zero] at he
    rw [← he]
    change G (I (f, 0)) = G (f, 0) - G (0, f)
    rw [← map_sub]
    apply congrArg G
    ext x <;> simp [I, doubledEmbedding]
  · have he := hagree ⟨I (0, 1), ⟨(0, 1), rfl⟩⟩
    change G (I (0, 1)) = doubledFunctional L x₀ (I (0, 1)) at he
    rw [doubledFunctional_embedding, map_zero, mul_one, zero_add] at he
    have hi : I (0, 1) = ((1 : C(X, ℝ)), 0) + (0, (1 : C(X, ℝ))) := by
      ext x <;> simp [I, doubledEmbedding]
    rw [hi, map_add] at he
    exact he

theorem exists_positive_functional_decomposition (L : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ P N : C(X, ℝ) →ₚ[ℝ] ℝ, ∀ f, L f = P f - N f := by
  obtain ⟨P, N, hrep, hbound⟩ := exists_positive_functional_decomposition_bounded L
  exact ⟨P, N, hrep⟩

end

end GlobalRegularization
