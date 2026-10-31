import GlobalRegularization.HilbertPositiveSupport
import Mathlib.Topology.Separation.Regular

/-! C¹ Urysohn cutoffs near arbitrary closed subsets of separable Hilbert
spaces. The sets need not be compact or have compact neighborhoods. -/

namespace GlobalRegularization

open Set Filter Function TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SeparableSpace H]

theorem exists_hilbert_C1_cutoff {K U : Set H} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : H → ℝ, ContDiff ℝ 1 χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨W, hW, hKW, hWU⟩ := normal_exists_closure_subset hK hU hKU
  obtain ⟨V, hV, hKV, hVW⟩ := normal_exists_closure_subset hK hW hKW
  obtain ⟨p, hps, hp, hpr⟩ := exists_hilbert_C1_positive_support hW
  obtain ⟨q, hqs, hq, hqr⟩ := exists_hilbert_C1_positive_support
    (s := (closure V)ᶜ) isClosed_closure.isOpen_compl
  have hp_pos {x : H} (hx : x ∈ W) : 0 < p x := by
    have hne : p x ≠ 0 := by rwa [← hps] at hx
    exact lt_of_le_of_ne (hpr x).1 (Ne.symm hne)
  have hq_pos {x : H} (hx : x ∉ closure V) : 0 < q x := by
    have hne : q x ≠ 0 := by
      have hm : x ∈ (closure V)ᶜ := hx
      rwa [← hqs] at hm
    exact lt_of_le_of_ne (hqr x).1 (Ne.symm hne)
  have hden (x : H) : 0 < p x + q x := by
    by_cases hx : x ∈ closure V
    · exact add_pos_of_pos_of_nonneg (hp_pos (hVW hx)) (hqr x).1
    · exact add_pos_of_nonneg_of_pos (hpr x).1 (hq_pos hx)
  let χ : H → ℝ := fun x => p x / (p x + q x)
  refine ⟨χ, hp.div (hp.add hq) (fun x => (hden x).ne'), ?_, ?_, ?_⟩
  · have hs : support χ ⊆ W := by
      intro x hx
      rw [← hps]
      change p x ≠ 0
      intro hpz
      exact hx (by simp [χ, hpz])
    exact (closure_mono hs).trans hWU
  · filter_upwards [hV.mem_nhdsSet.mpr hKV] with x hx
    have hqz : q x = 0 := by
      apply notMem_support.mp
      rw [hqs]
      exact not_not.mpr (subset_closure hx)
    exact (by simp only [χ, hqz, add_zero, div_self (hp_pos (hVW (subset_closure hx))).ne'])
  · intro x
    exact ⟨div_nonneg (hpr x).1 (hden x).le,
      (div_le_one (hden x)).mpr (le_add_of_nonneg_right (hqr x).1)⟩

end

end GlobalRegularization
