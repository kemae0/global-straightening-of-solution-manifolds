import GlobalRegularization.HilbertBumps
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.MetricSpace.Basic

/-! Positive C¹ functions with prescribed open support on a separable
Hilbert space. The construction sums genuine bumps with summable bounds
on the functions and their first derivatives. -/

namespace GlobalRegularization

open Set Filter Metric Function TopologicalSpace
open scoped Topology NNReal ContDiff

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SeparableSpace H]

theorem exists_hilbert_C1_positive_support {s : Set H} (hs : IsOpen s) :
    ∃ f : H → ℝ, support f = s ∧ ContDiff ℝ 1 f ∧ ∀ x, f x ∈ Icc 0 1 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨fun _ => 0, support_zero, contDiff_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩
  let ι := {f : H → ℝ // support f ⊆ s ∧ ContDiff ℝ 1 f ∧
    (∀ x, f x ∈ Icc 0 1) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ C}
  obtain ⟨T, hTc, hT⟩ : ∃ T : Set ι, T.Countable ∧ ⋃ f ∈ T, support (f : H → ℝ) = s := by
    have hcover : ⋃ f : ι, support (f : H → ℝ) = s := by
      apply Subset.antisymm (iUnion_subset (fun f => f.property.1))
      intro x hx
      obtain ⟨f, hfs, hf, hfr, hfx, hbound⟩ := exists_hilbert_C1_bump_in_nhds (hs.mem_nhds hx)
      let g : ι := ⟨f, hfs, hf, hfr, hbound⟩
      exact mem_iUnion_of_mem g (show x ∈ support (g : H → ℝ) by simpa only [g, mem_support, hfx] using one_ne_zero)
    obtain ⟨T, hTc, hT⟩ := isOpen_iUnion_countable
      (fun f : ι => support (f : H → ℝ)) (fun f => f.property.2.1.continuous.isOpen_support)
    exact ⟨T, hTc, hT.trans hcover⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ℕ → ι, T = range g₀ := by
    apply Countable.exists_eq_range hTc
    by_contra hTempty
    have he : T = ∅ := not_nonempty_iff_eq_empty.mp hTempty
    simp only [he, mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at hT
    exact hsne.ne_empty hT.symm
  let g : ℕ → H → ℝ := fun n => (g₀ n).val
  have hgs (n : ℕ) : support (g n) ⊆ s := (g₀ n).property.1
  have hg (n : ℕ) : ContDiff ℝ 1 (g n) := (g₀ n).property.2.1
  have hgr (n : ℕ) (x : H) : g n x ∈ Icc 0 1 := (g₀ n).property.2.2.1 x
  have hgb (n : ℕ) := (g₀ n).property.2.2.2
  choose C hC hbound using hgb
  have hcover (x : H) (hx : x ∈ s) : ∃ n, g n x ≠ 0 := by
    rw [← hT] at hx
    obtain ⟨f, hfT, hfx⟩ : ∃ f ∈ T, x ∈ support (f : H → ℝ) := by simpa only [mem_iUnion, exists_prop] using hx
    rw [hg₀] at hfT
    obtain ⟨n, rfl⟩ := hfT
    exact ⟨n, hfx⟩
  obtain ⟨δ, hδpos, c, hδsum, hc⟩ :
      ∃ δ : ℕ → ℝ≥0, (∀ n, 0 < δ n) ∧ ∃ c : ℝ≥0, HasSum δ c ∧ c < 1 :=
    NNReal.exists_pos_sum_of_countable one_ne_zero ℕ
  let M : ℕ → ℝ := fun n => max 1 (C n)
  let r : ℕ → ℝ := fun n => (δ n : ℝ) / M n
  have hM (n : ℕ) : 0 < M n := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hr (n : ℕ) : 0 < r n := div_pos (hδpos n) (hM n)
  have hkbound (k : ℕ) (hk : (k : ℕ∞) ≤ 1) (n : ℕ) (x : H) :
      ‖iteratedFDeriv ℝ k (r n • g n) x‖ ≤ δ n := by
    have hbase : ‖iteratedFDeriv ℝ k (g n) x‖ ≤ M n := by
      have hk' : k ≤ 1 := by exact_mod_cast hk
      interval_cases k
      · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hgr n x).1]
        exact (hgr n x).2.trans (le_max_left _ _)
      · rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
        exact (hbound n x).trans (le_max_right _ _)
    rw [iteratedFDeriv_const_smul_apply]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr n)]
      calc
        _ ≤ r n * M n := mul_le_mul_of_nonneg_left hbase (hr n).le
        _ = δ n := div_mul_cancel₀ _ (hM n).ne'
    · exact (hg n).contDiffAt.of_le (mod_cast hk)
  have hsum (x : H) : Summable (fun n => (r n • g n) x) := by
    apply Summable.of_nnnorm_bounded hδsum.summable
    intro n
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa only [norm_iteratedFDeriv_zero] using hkbound 0 (by norm_num) n x
  refine ⟨fun x => ∑' n, (r n • g n) x, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      by_contra hxs
      have hz (n : ℕ) : g n x = 0 := by
        by_contra hne
        exact hxs (hgs n hne)
      exact hx (by simp [hz])
    · intro x hx
      obtain ⟨n, hn⟩ := hcover x hx
      have hp : 0 < r n * g n x := mul_pos (hr n) (lt_of_le_of_ne (hgr n x).1 (Ne.symm hn))
      exact ne_of_gt ((hsum x).tsum_pos (fun i => mul_nonneg (hr i).le (hgr i x).1) n hp)
  · exact contDiff_tsum (fun n => (hg n).const_smul (r n))
      (fun k hk => (NNReal.hasSum_coe.mpr hδsum).summable) (fun k n x hk => hkbound k hk n x)
  · intro x
    refine ⟨tsum_nonneg (fun n => mul_nonneg (hr n).le (hgr n x).1), ?_⟩
    have hd : HasSum (fun n => (δ n : ℝ)) c := NNReal.hasSum_coe.mpr hδsum
    apply (Summable.tsum_le_tsum _ (hsum x) hd.summable).trans (by
      rw [hd.tsum_eq]
      exact_mod_cast hc.le)
    intro n
    exact (le_abs_self _).trans (by simpa only [norm_iteratedFDeriv_zero] using hkbound 0 (by norm_num) n x)

end

end GlobalRegularization
