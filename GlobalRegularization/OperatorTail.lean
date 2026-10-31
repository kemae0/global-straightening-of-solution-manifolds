import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

/-!
# Nilpotent part with an annihilated small remainder

The factorization here avoids a spectral-radius formula for invertibility.
The hypotheses are algebraic approximation data, not the conclusion of the
paper's analytic construction.
-/

namespace GlobalRegularization

open Filter
open scoped Topology

section Ring

variable {A : Type*} [Ring A]

theorem one_add_eq_mul_of_mul_eq_zero {a b : A} (hab : a * b = 0) :
    1 + (a + b) = (1 + a) * (1 + b) := by
  simp [add_mul, mul_add, hab, add_assoc, add_comm, add_left_comm]

theorem isUnit_one_add_of_nilpotent_remainder {a b : A}
    (ha : IsNilpotent a) (hab : a * b = 0) (hb : IsUnit (1 + b)) :
    IsUnit (1 + (a + b)) := by
  rw [one_add_eq_mul_of_mul_eq_zero hab]
  exact ha.isUnit_one_add.mul hb

end Ring

section BanachAlgebra

variable {A : Type*} [NormedRing A] [CompleteSpace A]

theorem isUnit_one_add_of_nilpotent_small_remainder {a b : A}
    (ha : IsNilpotent a) (hab : a * b = 0) (hb : ‖b‖ < 1) :
    IsUnit (1 + (a + b)) := by
  apply isUnit_one_add_of_nilpotent_remainder ha hab
  simpa using (isUnit_one_sub_of_norm_lt_one (x := -b) (by simpa using hb))

theorem isUnit_one_add_of_nilpotent_approximation
    (K : A) (Kfin R : ℕ → A)
    (hsplit : ∀ n, K = Kfin n + R n)
    (hnil : ∀ n, IsNilpotent (Kfin n))
    (hann : ∀ n, Kfin n * R n = 0)
    (hsmall : Tendsto R atTop (𝓝 0)) :
    IsUnit (1 + K) := by
  have hevent : ∀ᶠ n in atTop, ‖R n‖ < 1 := by
    have hn := hsmall.norm
    exact (tendsto_order.1 hn).2 1 (by simp)
  obtain ⟨n, hn⟩ := hevent.exists
  rw [hsplit n]
  exact isUnit_one_add_of_nilpotent_small_remainder (hnil n) (hann n) hn

end BanachAlgebra

section ScalarAlgebra

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

theorem isUnit_one_add_smul_of_nilpotent_approximation
    (K : A) (Kfin R : ℕ → A)
    (hsplit : ∀ n, K = Kfin n + R n)
    (hnil : ∀ n, IsNilpotent (Kfin n))
    (hann : ∀ n, Kfin n * R n = 0)
    (hsmall : Tendsto R atTop (𝓝 0)) (c : 𝕜) :
    IsUnit (1 + c • K) := by
  apply isUnit_one_add_of_nilpotent_approximation (c • K)
    (fun n => c • Kfin n) (fun n => c • R n)
  · intro n; rw [hsplit n, smul_add]
  · intro n; exact (hnil n).smul c
  · intro n; simp [hann n]
  · simpa using hsmall.const_smul c

theorem spectrum_subset_zero_of_nilpotent_approximation
    (K : A) (Kfin R : ℕ → A)
    (hsplit : ∀ n, K = Kfin n + R n)
    (hnil : ∀ n, IsNilpotent (Kfin n))
    (hann : ∀ n, Kfin n * R n = 0)
    (hsmall : Tendsto R atTop (𝓝 0)) :
    spectrum 𝕜 K ⊆ {0} := by
  intro z hz
  by_contra hzero
  have hz0 : z ≠ 0 := by simpa using hzero
  have hu := isUnit_one_add_smul_of_nilpotent_approximation
    K Kfin R hsplit hnil hann hsmall (-z⁻¹)
  have huv : IsUnit (z • (1 + (-z⁻¹) • K)) := by
    simpa only [Units.smul_def, Units.val_mk0] using
      (IsUnit.smul (Units.mk0 z hz0) hu)
  have heq : z • (1 + (-z⁻¹) • K) = algebraMap 𝕜 A z - K := by
    simp [smul_add, smul_smul, hz0, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
  exact (spectrum.mem_iff.mp hz) (heq ▸ huv)

theorem spectralRadius_eq_zero_of_nilpotent_approximation
    (K : A) (Kfin R : ℕ → A)
    (hsplit : ∀ n, K = Kfin n + R n)
    (hnil : ∀ n, IsNilpotent (Kfin n))
    (hann : ∀ n, Kfin n * R n = 0)
    (hsmall : Tendsto R atTop (𝓝 0)) :
    spectralRadius 𝕜 K = 0 := by
  have hs := spectrum_subset_zero_of_nilpotent_approximation
    (𝕜 := 𝕜) K Kfin R hsplit hnil hann hsmall
  apply le_antisymm _ (zero_le _)
  simp only [spectralRadius, iSup_le_iff]
  intro z hz
  have hz0 : z = 0 := hs hz
  simp [hz0]

end ScalarAlgebra

section ComplexAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [Nontrivial A]

theorem spectrum_eq_zero_of_nilpotent_approximation
    (K : A) (Kfin R : ℕ → A)
    (hsplit : ∀ n, K = Kfin n + R n)
    (hnil : ∀ n, IsNilpotent (Kfin n))
    (hann : ∀ n, Kfin n * R n = 0)
    (hsmall : Tendsto R atTop (𝓝 0)) :
    spectrum ℂ K = {0} := by
  apply Set.Subset.antisymm
  · exact spectrum_subset_zero_of_nilpotent_approximation
      K Kfin R hsplit hnil hann hsmall
  · obtain ⟨z, hz⟩ := spectrum.nonempty K
    have hz0 : z = 0 := spectrum_subset_zero_of_nilpotent_approximation
      K Kfin R hsplit hnil hann hsmall hz
    simpa [hz0] using Set.singleton_subset_iff.mpr hz

theorem spectrum_one_add_eq_one_of_nilpotent_approximation
    (K : A) (Kfin R : ℕ → A)
    (hsplit : ∀ n, K = Kfin n + R n)
    (hnil : ∀ n, IsNilpotent (Kfin n))
    (hann : ∀ n, Kfin n * R n = 0)
    (hsmall : Tendsto R atTop (𝓝 0)) :
    spectrum ℂ (1 + K) = {1} := by
  rw [← map_one (algebraMap ℂ A), ← spectrum.singleton_add_eq]
  rw [spectrum_eq_zero_of_nilpotent_approximation K Kfin R hsplit hnil hann hsmall]
  simp

end ComplexAlgebra

end GlobalRegularization
