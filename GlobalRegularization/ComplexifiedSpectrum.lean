import GlobalRegularization.RealComplexification
import GlobalRegularization.TriangularLimit

/-! Spectral consequences for the actual complexification of a real
operator with the proved triangular finite-part/remainder decomposition. -/

namespace GlobalRegularization

open Filter
open scoped Topology

noncomputable section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem complexified_spectrum_subset_of_triangular_limit
    (Q : ℕ → B →L[ℝ] E) (A : ℕ → E →L[ℝ] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0)
    (K : E →L[ℝ] E) (hK : Tendsto (triangularPartial Q A) atTop (𝓝 K)) :
    spectrum ℂ (RealComplexification.map K) ⊆ {0} := by
  let H := RealComplexification.mapEndRingHom (E := E)
  let R := fun n => K - triangularPartial Q A n
  apply spectrum_subset_zero_of_nilpotent_approximation (H K) (fun n => H (triangularPartial Q A n))
    (fun n => H (R n))
  · intro n
    rw [← map_add]
    congr 1
    dsimp only [R]
    abel
  · intro n
    exact (triangularPartial_nilpotent Q A hann n).map H
  · intro n
    rw [← map_mul, triangularPartial_annihilates_remainder Q A hann K hK n, map_zero]
  · have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K)).sub hK
    simp only [sub_self] at ht
    have hm := (RealComplexification.mapL (E := E) (F := E)).continuous.tendsto 0 |>.comp ht
    simpa only [RealComplexification.mapL_apply, RealComplexification.map_zero] using hm

theorem complexified_spectrum_one_add_subset_of_triangular_limit
    (Q : ℕ → B →L[ℝ] E) (A : ℕ → E →L[ℝ] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0)
    (K : E →L[ℝ] E) (hK : Tendsto (triangularPartial Q A) atTop (𝓝 K)) :
    spectrum ℂ (RealComplexification.map (1 + K)) ⊆ {1} := by
  have hm : RealComplexification.map (1 + K) = 1 + RealComplexification.map K :=
    by simpa only [map_one] using (RealComplexification.mapEndRingHom (E := E)).map_add 1 K
  rw [hm, ← map_one (algebraMap ℂ _), ← spectrum.singleton_add_eq]
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  have hb0 : b = 0 := complexified_spectrum_subset_of_triangular_limit Q A hann K hK hb
  simpa only [Set.mem_singleton_iff, hb0, add_zero] using ha

theorem complexified_spectrum_one_add_eq_of_triangular_limit [Nontrivial E]
    (Q : ℕ → B →L[ℝ] E) (A : ℕ → E →L[ℝ] B)
    (hann : ∀ i j, i ≤ j → (A i).comp (Q j) = 0)
    (K : E →L[ℝ] E) (hK : Tendsto (triangularPartial Q A) atTop (𝓝 K)) :
    spectrum ℂ (RealComplexification.map (1 + K)) = {1} := by
  have hs := complexified_spectrum_one_add_subset_of_triangular_limit Q A hann K hK
  apply Set.Subset.antisymm hs
  obtain ⟨z, hz⟩ := spectrum.nonempty (RealComplexification.map (1 + K))
  have hz1 : z = 1 := hs hz
  exact Set.singleton_subset_iff.mpr (hz1 ▸ hz)

end

end GlobalRegularization
