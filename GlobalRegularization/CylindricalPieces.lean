import GlobalRegularization.FiniteCutoff

/-! Bounded cylindrical `C¹` pieces on arbitrary open domains.
The compact core uses separation from every point of the complement;
this also handles the full-domain case without a distance-to-empty-set
convention. Local capture of a family of cores is a separate step. -/

namespace GlobalRegularization

open Set Filter
open scoped Topology

noncomputable section

variable {E F B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def approximationCore (U : Set E) (j : F →L[ℝ] E) (n : ℕ) : Set F :=
  {z | ‖z‖ ≤ (n : ℝ) ∧ ∀ y : E, y ∉ U → 1 / (n + 1 : ℝ) ≤ dist (j z) y}

theorem approximationCore_isCompact [FiniteDimensional ℝ F]
    (U : Set E) (j : F →L[ℝ] E) (n : ℕ) : IsCompact (approximationCore U j n) := by
  have hnorm : IsClosed {z : F | ‖z‖ ≤ (n : ℝ)} := isClosed_le continuous_norm continuous_const
  have hsep : IsClosed {z : F | ∀ y : E, y ∉ U → 1 / (n + 1 : ℝ) ≤ dist (j z) y} := by
    simp_rw [Set.setOf_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    exact isClosed_le continuous_const (j.continuous.dist continuous_const)
  have hclosed : IsClosed (approximationCore U j n) := hnorm.inter hsep
  apply (isCompact_closedBall (0 : F) (n : ℝ)).of_isClosed_subset hclosed
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1

theorem approximationCore_subset (U : Set E) (j : F →L[ℝ] E) (n : ℕ) :
    approximationCore U j n ⊆ j ⁻¹' U := by
  intro z hz
  by_contra hzU
  have h := hz.2 (j z) hzU
  rw [dist_self] at h
  have hp : 0 < 1 / (n + 1 : ℝ) := by positivity
  linarith

theorem exists_bounded_cylindrical_piece
    (U : Set E) (hU : IsOpen U) (f : E → B) (hf : ContDiffOn ℝ 1 f U)
    (P : E →L[ℝ] E) [FiniteDimensional ℝ (LinearMap.range P)] (n : ℕ) :
    ∃ fn : E → B, ContDiff ℝ 1 fn ∧ Bornology.IsBounded (range fn) ∧
      (∃ hat : LinearMap.range P → B, ContDiff ℝ 1 hat ∧ ∀ x, fn x = hat (P.rangeRestrict x)) ∧
      ∀ x, P.rangeRestrict x ∈ approximationCore U (LinearMap.range P).subtypeL n → fn x = f (P x) := by
  let j : LinearMap.range P →L[ℝ] E := (LinearMap.range P).subtypeL
  have hV : IsOpen (j ⁻¹' U) := hU.preimage j.continuous
  have hfj : ContDiffOn ℝ 1 (fun z => f (j z)) (j ⁻¹' U) :=
    hf.comp j.contDiff.contDiffOn (fun z hz => hz)
  obtain ⟨hat, hhat, hbounded, hagree⟩ := exists_bounded_C1_extension_near_compact
    (approximationCore_isCompact U j n) hV (approximationCore_subset U j n)
    (fun z => f (j z)) hfj
  refine ⟨fun x => hat (P.rangeRestrict x), hhat.comp P.rangeRestrict.contDiff, ?_,
    ⟨hat, hhat, fun x => rfl⟩, ?_⟩
  · apply hbounded.subset
    rintro y ⟨x, rfl⟩
    exact ⟨P.rangeRestrict x, rfl⟩
  · intro x hx
    exact hagree.self_of_nhdsSet (P.rangeRestrict x) hx

end

end GlobalRegularization
