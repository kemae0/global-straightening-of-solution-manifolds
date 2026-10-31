import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! A complete complexification of a real Banach space. It is realized as
the real continuous linear maps from ℂ, with complex scalars acting by
precomposition. The operator norm is invariant under complex rotations. -/

namespace GlobalRegularization

noncomputable section

def RealComplexification (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := ℂ →L[ℝ] E

namespace RealComplexification

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

instance : NormedAddCommGroup (RealComplexification E) :=
  inferInstanceAs (NormedAddCommGroup (ℂ →L[ℝ] E))

instance : NormedSpace ℝ (RealComplexification E) :=
  inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] E))

instance [CompleteSpace E] : CompleteSpace (RealComplexification E) :=
  inferInstanceAs (CompleteSpace (ℂ →L[ℝ] E))

instance : CoeFun (RealComplexification E) (fun _ => ℂ → E) :=
  ⟨fun f z => (ContinuousLinearMap.toLinearMap (f : ℂ →L[ℝ] E)) z⟩

@[ext] theorem ext {f g : RealComplexification E} (h : ∀ z, f z = g z) : f = g :=
  ContinuousLinearMap.ext h

@[simp] theorem add_apply (f g : RealComplexification E) (z : ℂ) : (f + g) z = f z + g z := rfl
@[simp] theorem zero_apply (z : ℂ) : (0 : RealComplexification E) z = 0 := rfl
@[simp] theorem real_smul_apply (r : ℝ) (f : RealComplexification E) (z : ℂ) : (r • f) z = r • f z := rfl

def scalarArgument (c : ℂ) : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ c

instance : SMul ℂ (RealComplexification E) :=
  ⟨fun c f => (f : ℂ →L[ℝ] E).comp (scalarArgument c)⟩

@[simp] theorem complex_smul_apply (c : ℂ) (f : RealComplexification E) (z : ℂ) :
    (c • f : RealComplexification E) z = f (c * z) := rfl

instance : Module ℂ (RealComplexification E) where
  one_smul f := by
    apply ext
    intro z
    change f ((1 : ℂ) * z) = f z
    rw [one_mul]
  mul_smul a b f := by
    apply ext
    intro z
    change f ((a * b) * z) = f (b * (a * z))
    exact congrArg f (by ring)
  smul_zero a := by apply ContinuousLinearMap.ext; intro z; rfl
  smul_add a f g := by apply ContinuousLinearMap.ext; intro z; rfl
  add_smul a b f := by
    apply ext
    intro z
    change f ((a + b) * z) = f (a * z) + f (b * z)
    rw [add_mul]
    exact (f : ℂ →L[ℝ] E).map_add _ _
  zero_smul f := by
    apply ext
    intro z
    change f ((0 : ℂ) * z) = 0
    rw [zero_mul]
    exact (f : ℂ →L[ℝ] E).map_zero

instance : NormedSpace ℂ (RealComplexification E) where
  norm_smul_le c f := by
    change ‖(f : ℂ →L[ℝ] E).comp (scalarArgument c)‖ ≤ ‖c‖ * ‖f‖
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hc : ‖scalarArgument c‖ ≤ ‖c‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) (fun z => by
        change ‖c * z‖ ≤ ‖c‖ * ‖z‖
        exact (norm_mul c z).le)
    exact (mul_le_mul_of_nonneg_left hc (norm_nonneg f)).trans_eq (mul_comm _ _)

instance : IsScalarTower ℝ ℂ (RealComplexification E) where
  smul_assoc r c f := by
    apply ContinuousLinearMap.ext
    intro z
    change f ((r • c) * z) = r • f (c * z)
    rw [smul_mul_assoc]
    exact (f : ℂ →L[ℝ] E).map_smul _ _

instance : SMulCommClass ℝ ℂ (RealComplexification E) where
  smul_comm r c f := by
    apply ContinuousLinearMap.ext
    intro z
    rfl

def embed (x : E) : RealComplexification E := Complex.reCLM.smulRight x

@[simp] theorem embed_apply (x : E) (z : ℂ) : embed x z = z.re • x := rfl

theorem embed_injective : Function.Injective (embed : E → RealComplexification E) := by
  intro x y hxy
  have h := congrArg (fun f : RealComplexification E => f 1) hxy
  simpa only [embed_apply, Complex.one_re, one_smul] using h

instance [Nontrivial E] : Nontrivial (RealComplexification E) :=
  Function.Injective.nontrivial (f := embed) embed_injective

def map (L : E →L[ℝ] F) : RealComplexification E →L[ℂ] RealComplexification F :=
  { toFun := fun f => L.comp f
    map_add' := fun f g => by apply ContinuousLinearMap.ext; intro z; exact L.map_add _ _
    map_smul' := fun c f => by apply ContinuousLinearMap.ext; intro z; rfl
    cont := by
      exact (ContinuousLinearMap.compL ℝ ℂ E F L).continuous }

@[simp] theorem map_apply (L : E →L[ℝ] F) (f : RealComplexification E) (z : ℂ) : map L f z = L (f z) := rfl

theorem norm_map_le (L : E →L[ℝ] F) : ‖map L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (fun f => ContinuousLinearMap.opNorm_comp_le L f)

@[simp] theorem map_embed (L : E →L[ℝ] F) (x : E) : map L (embed x) = embed (L x) := by
  apply ContinuousLinearMap.ext
  intro z
  exact L.map_smul _ _

@[simp] theorem map_zero : map (0 : E →L[ℝ] F) = 0 := by ext f z; rfl

@[simp] theorem map_add (L M : E →L[ℝ] F) : map (L + M) = map L + map M := by ext f z; rfl

@[simp] theorem map_id : map (ContinuousLinearMap.id ℝ E) = ContinuousLinearMap.id ℂ (RealComplexification E) := by
  ext f z
  rfl

@[simp] theorem map_comp (L : F →L[ℝ] G) (M : E →L[ℝ] F) :
    map (L.comp M) = (map L).comp (map M) := by ext f z; rfl

def mapLinear : (E →L[ℝ] F) →ₗ[ℝ] (RealComplexification E →L[ℂ] RealComplexification F) :=
  { toFun := map
    map_add' := map_add
    map_smul' := fun r L => by ext f z; rfl }

def mapL : (E →L[ℝ] F) →L[ℝ] (RealComplexification E →L[ℂ] RealComplexification F) :=
  mapLinear.mkContinuous 1 (fun L => by simpa only [one_mul] using norm_map_le L)

@[simp] theorem mapL_apply (L : E →L[ℝ] F) : mapL L = map L := rfl

def mapEndRingHom : (E →L[ℝ] E) →+* (RealComplexification E →L[ℂ] RealComplexification E) where
  toFun := map
  map_one' := map_id
  map_mul' := map_comp
  map_zero' := map_zero
  map_add' := map_add

@[simp] theorem mapEndRingHom_apply (L : E →L[ℝ] E) : mapEndRingHom L = map L := rfl

end RealComplexification

end

end GlobalRegularization
