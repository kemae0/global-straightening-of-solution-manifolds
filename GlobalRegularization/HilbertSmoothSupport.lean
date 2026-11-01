import GlobalRegularization.HilbertSmoothBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.MetricSpace.Basic

/-! Infinitely smooth positive functions with prescribed open support on
a separable real Hilbert space. Higher derivative bounds are obtained on
bounded balls directly, without assuming those balls compact. -/

namespace GlobalRegularization

open Set Filter Metric Function TopologicalSpace
open scoped Topology NNReal ContDiff

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SeparableSpace H]

theorem exists_hilbert_smooth_positive_support {s : Set H} (hs : IsOpen s) :
    ∃ f : H → ℝ, support f = s ∧ ContDiff ℝ ∞ f ∧ ∀ x, f x ∈ Icc 0 1 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨fun _ => 0, support_zero, contDiff_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩
  let ι := {p : H × ℝ // 0 < p.2 ∧ ball p.1 p.2 ⊆ s}
  let b : ι → H → ℝ := fun p => hilbertBump p.val.1 p.val.2
  have hb (p : ι) : ContDiff ℝ ∞ (b p) := hilbertBump_contDiff _ _
  have hbs (p : ι) : support (b p) ⊆ s :=
    (hilbertBump_support_subset _ _ p.property.1).trans p.property.2
  have hbr (p : ι) (x : H) : b p x ∈ Icc 0 1 :=
    ⟨hilbertBump_nonneg _ _ _, hilbertBump_le_one _ _ _⟩
  have hcover : ⋃ p : ι, support (b p) = s := by
    apply Subset.antisymm (iUnion_subset hbs)
    intro x hx
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
    let p : ι := ⟨(x, r), hr, hrs⟩
    have hone : b p x = 1 := hilbertBump_one_of_dist_le x r hr x (by simp; positivity)
    exact mem_iUnion_of_mem p (show x ∈ support (b p) by rw [mem_support, hone]; exact one_ne_zero)
  obtain ⟨T, hTc, hT⟩ := isOpen_iUnion_countable (fun p : ι => support (b p))
    (fun p => (hb p).continuous.isOpen_support)
  have hTcover : ⋃ p ∈ T, support (b p) = s := hT.trans hcover
  have hTne : T.Nonempty := by
    by_contra he
    have hempty : T = ∅ := not_nonempty_iff_eq_empty.mp he
    simp only [hempty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at hTcover
    exact hsne.ne_empty hTcover.symm
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ℕ → ι, T = range g₀ := Countable.exists_eq_range hTc hTne
  let g : ℕ → H → ℝ := fun n => b (g₀ n)
  have hg (n : ℕ) : ContDiff ℝ ∞ (g n) := hb (g₀ n)
  have hgr (n : ℕ) (x : H) : g n x ∈ Icc 0 1 := hbr (g₀ n) x
  have hgs (n : ℕ) : support (g n) ⊆ s := hbs (g₀ n)
  have hgb (n k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k (g n) x‖ ≤ C :=
    hilbertBump_all_derivatives_bounded _ _ (g₀ n).property.1 k
  choose C hC hbound using hgb
  have hcover' (x : H) (hx : x ∈ s) : ∃ n, g n x ≠ 0 := by
    rw [← hTcover] at hx
    obtain ⟨p, hpT, hpx⟩ : ∃ p ∈ T, x ∈ support (b p) := by
      simpa only [mem_iUnion, exists_prop] using hx
    rw [hg₀] at hpT
    obtain ⟨n, rfl⟩ := hpT
    exact ⟨n, hpx⟩
  obtain ⟨δ, hδpos, c, hδsum, hc⟩ :
      ∃ δ : ℕ → ℝ≥0, (∀ n, 0 < δ n) ∧ ∃ c : ℝ≥0, HasSum δ c ∧ c < 1 :=
    NNReal.exists_pos_sum_of_countable one_ne_zero ℕ
  let M : ℕ → ℝ := fun n => 1 + ∑ k ∈ Finset.range (n + 1), C n k
  let r : ℕ → ℝ := fun n => (δ n : ℝ) / M n
  have hM (n : ℕ) : 0 < M n := by
    dsimp only [M]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun k _ => hC n k))
  have hr (n : ℕ) : 0 < r n := div_pos (hδpos n) (hM n)
  have hkbound (n k : ℕ) (hk : k ≤ n) (x : H) :
      ‖iteratedFDeriv ℝ k (r n • g n) x‖ ≤ δ n := by
    have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsmall : C n k ≤ M n :=
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.range (n + 1)) => hC n j) hmem).trans
        (le_add_of_nonneg_left zero_le_one)
    rw [iteratedFDeriv_const_smul_apply ((hg n).contDiffAt.of_le (mod_cast le_top)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (hr n)]
    calc
      _ ≤ r n * M n := mul_le_mul_of_nonneg_left ((hbound n k x).trans hsmall) (hr n).le
      _ = δ n := div_mul_cancel₀ _ (hM n).ne'
  have hsum (x : H) : Summable (fun n => (r n • g n) x) := by
    apply Summable.of_nnnorm_bounded hδsum.summable
    intro n
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa only [norm_iteratedFDeriv_zero] using hkbound n 0 (Nat.zero_le n) x
  refine ⟨fun x => ∑' n, (r n • g n) x, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      by_contra hxs
      have hz (n : ℕ) : g n x = 0 := by
        by_contra hne
        exact hxs (hgs n hne)
      exact hx (by simp [hz])
    · intro x hx
      obtain ⟨n, hn⟩ := hcover' x hx
      have hp : 0 < r n * g n x := mul_pos (hr n) (lt_of_le_of_ne (hgr n x).1 (Ne.symm hn))
      exact ne_of_gt ((hsum x).tsum_pos (fun i => mul_nonneg (hr i).le (hgr i x).1) n hp)
  · apply contDiff_tsum_of_eventually (fun n => (hg n).const_smul (r n))
      (fun k _ => (NNReal.hasSum_coe.mpr hδsum).summable)
    intro k _
    simp only [Nat.cofinite_eq_atTop, eventually_atTop]
    exact ⟨k, fun n hn x => hkbound n k hn x⟩
  · intro x
    refine ⟨tsum_nonneg (fun n => mul_nonneg (hr n).le (hgr n x).1), ?_⟩
    have hd : HasSum (fun n => (δ n : ℝ)) c := NNReal.hasSum_coe.mpr hδsum
    apply (Summable.tsum_le_tsum _ (hsum x) hd.summable).trans (by
      rw [hd.tsum_eq]
      exact_mod_cast hc.le)
    intro n
    exact (le_abs_self _).trans (by simpa only [norm_iteratedFDeriv_zero] using hkbound n 0 (Nat.zero_le n) x)

end

end GlobalRegularization
