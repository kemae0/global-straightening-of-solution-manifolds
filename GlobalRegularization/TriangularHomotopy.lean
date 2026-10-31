import GlobalRegularization.TriangularLimit
import GlobalRegularization.Triangular
import GlobalRegularization.GlobalInverse

/-! Affine homotopies of triangular coordinates. Every real parameter
gives an injective local diffeomorphism; dependence on the parameter and
the history is jointly continuously differentiable. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def affineHomotopy (A : E → E) (s : ℝ) (x : E) : E := x + s • (A x - x)

/-- A jointly `C¹` affine isotopy through global charts. Requiring all
real parameters is stronger than the manuscript's interval `[0,1]`. -/
def C1Straightening.HasAffineIsotopy
    {U : Set E} {D : E →L[ℝ] B} {f : E → B} (chart : C1Straightening U D f) : Prop :=
  ContDiffOn ℝ 1 (fun p : ℝ × E => affineHomotopy chart.forward p.1 p.2) (univ.prod U) ∧
    ∀ s : ℝ, ∃ slice : C1Straightening U D (fun x => s • f x),
      slice.forward = affineHomotopy chart.forward s

omit [CompleteSpace E] in
theorem triangularPartial_smul (Q : ℕ → B →L[ℝ] E) (L : ℕ → E →L[ℝ] B)
    (s : ℝ) (n : ℕ) :
    triangularPartial Q (fun i => s • L i) n = s • triangularPartial Q L n := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [triangularPartial, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, Finset.smul_sum]

theorem isUnit_one_add_smul_triangular_limit
    (Q : ℕ → B →L[ℝ] E) (L : ℕ → E →L[ℝ] B)
    (hann : ∀ i j, i ≤ j → (L i).comp (Q j) = 0)
    (K : E →L[ℝ] E) (hK : Tendsto (triangularPartial Q L) atTop (𝓝 K)) (s : ℝ) :
    IsUnit (1 + s • K) := by
  refine isUnit_one_add_triangular_limit Q (fun i => s • L i) ?_ (s • K) ?_
  · intro i j hij
    simp only [ContinuousLinearMap.smul_comp, hann i j hij, smul_zero]
  · change Tendsto (fun n => triangularPartial Q (fun i => s • L i) n) atTop (𝓝 (s • K))
    simpa only [triangularPartial_smul] using hK.const_smul s

omit [CompleteSpace E] in
theorem affineHomotopy_joint_C1 {U : Set E} {A : E → E} (hA : ContDiffOn ℝ 1 A U) :
    ContDiffOn ℝ 1 (fun p : ℝ × E => affineHomotopy A p.1 p.2) (univ.prod U) := by
  exact contDiffOn_snd.add (contDiffOn_fst.smul
    ((hA.comp contDiffOn_snd (fun p hp => hp.2)).sub contDiffOn_snd))

omit [CompleteSpace E] [NormedAddCommGroup B] [NormedSpace ℝ B] in
theorem affineHomotopy_injective
    {U : Set E} (A : E → E) (O : ℕ → E →L[ℝ] E) (fm : ℕ → E → B)
    (c : ℕ → ℕ → B → E)
    (htri : ∀ j x, x ∈ U → O j (A x) = O j x + ∑ i ∈ Finset.range j, c j i (fm i x))
    (hfactor : ∀ i x y, x ∈ U → y ∈ U → O i x = O i y → fm i x = fm i y)
    (hseparate : ∀ x y, x ∈ U → y ∈ U → (∀ j, O j x = O j y) → x = y)
    (s : ℝ) : Set.InjOn (affineHomotopy A s) U := by
  apply triangular_injective_on U (affineHomotopy A s) (fun j => O j) fm
    (fun j i a => s • c j i a) _ hfactor hseparate
  intro j x hx
  simp only [affineHomotopy, map_add, map_smul, map_sub, htri j x hx,
    add_sub_cancel_left, Finset.smul_sum]

theorem affineHomotopy_invertible_derivative
    {U : Set E} (hU : IsOpen U) {A : E → E} (hA : ContDiffOn ℝ 1 A U)
    (Q : ℕ → B →L[ℝ] E) (L : E → ℕ → E →L[ℝ] B)
    (hann : ∀ x ∈ U, ∀ i j, i ≤ j → (L x i).comp (Q j) = 0)
    (hlim : ∀ x ∈ U, Tendsto (triangularPartial Q (L x)) atTop
      (𝓝 (fderiv ℝ A x - 1))) (s : ℝ) :
    ∀ x ∈ U, ∃ T : E ≃L[ℝ] E, HasFDerivAt (affineHomotopy A s) (T : E →L[ℝ] E) x := by
  intro x hx
  have hu := isUnit_one_add_smul_triangular_limit Q (L x) (hann x hx)
    (fderiv ℝ A x - 1) (hlim x hx) s
  refine ⟨ContinuousLinearEquiv.ofUnit hu.unit, ?_⟩
  have heq : (ContinuousLinearEquiv.ofUnit hu.unit : E →L[ℝ] E) =
      1 + s • (fderiv ℝ A x - 1) := hu.unit_spec
  rw [heq]
  have hd := ((hA.differentiableOn le_rfl x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  exact (hasFDerivAt_id x).add ((hd.sub (hasFDerivAt_id x)).const_smul s)

end

end GlobalRegularization
