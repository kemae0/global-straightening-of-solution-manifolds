import GlobalRegularization.HilbertCutoff
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The smooth partition-of-unity assertion used in the Hilbert proof,
with no finite-dimensionality or local compactness assumption. -/

namespace GlobalRegularization

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SeparableSpace H]

theorem exists_hilbert_smooth_partition_of_unity {ι : Type*}
    (U : ι → Set H) (hU : ∀ i, IsOpen (U i)) (hcover : (univ : Set H) ⊆ ⋃ i, U i) :
    ∃ p : SmoothPartitionOfUnity ι 𝓘(ℝ, H) H univ, p.IsSubordinate U := by
  have h01 : ∀ s t : Set H, IsClosed s → IsClosed t → Disjoint s t →
      ∃ f : C(H, ℝ), ContDiff ℝ ∞ f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc 0 1 := by
    intro s t hs ht hdis
    have hts : t ⊆ sᶜ := fun x hx hsx => Set.disjoint_left.mp hdis hsx hx
    obtain ⟨f, hf, hsupport, hone, hr⟩ := exists_hilbert_smooth_cutoff ht hs.isOpen_compl hts
    refine ⟨⟨f, hf.continuous⟩, hf, ?_, ?_, hr⟩
    · intro x hx
      change f x = 0
      apply notMem_support.mp
      intro hm
      exact (hsupport (subset_closure hm)) hx
    · intro x hx
      have hmem : x ∈ {y : H | f y = 1} := mem_of_mem_nhds ((nhds_le_nhdsSet hx) hone)
      exact hmem
  obtain ⟨b, hb, hsub⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun f : H → ℝ => ContDiff ℝ ∞ f) h01 isClosed_univ U hU hcover
  refine ⟨b.toSmoothPartitionOfUnity (fun i => (hb i).contMDiff), ?_⟩
  exact hsub.toSmoothPartitionOfUnity (fun i => (hb i).contMDiff)

end

end GlobalRegularization
