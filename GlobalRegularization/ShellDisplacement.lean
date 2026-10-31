import GlobalRegularization.ShellCoordinate

/-! The continuous-history displacement estimate. The second series is
absolutely convergent in the continuous-history norm; its identity with
the already constructed `C¹` coordinate is proved by telescoping. -/

namespace GlobalRegularization

open Set Filter
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem norm_terminalCorrection_value_le (δ : ℝ) (hδ : 0 < δ) (a : B) :
    ‖historyInclusion h B (terminalCorrection h B δ hδ a)‖ ≤ δ / 2 * ‖a‖ := by
  exact (((historyInclusion h B).comp (terminalCorrection h B δ hδ)).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (terminalCorrection_small h B δ hδ) (norm_nonneg a))

theorem norm_terminalShell_value_le
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (i : ℕ) (a : B) :
    ‖historyInclusion h B (terminalShell h B δ hδ i a)‖ ≤ δ i * ‖a‖ := by
  have hmono := shrinkingWidths_antitone δ hδ hstep (Nat.le_succ i)
  calc
    _ ≤ ‖historyInclusion h B (terminalCorrection h B (δ i) (hδ i) a)‖ +
      ‖historyInclusion h B (terminalCorrection h B (δ (i + 1)) (hδ (i + 1)) a)‖ := by
        simpa only [terminalShell, ContinuousLinearMap.sub_apply, map_sub] using norm_sub_le
          (historyInclusion h B (terminalCorrection h B (δ i) (hδ i) a))
          (historyInclusion h B (terminalCorrection h B (δ (i + 1)) (hδ (i + 1)) a))
    _ ≤ δ i / 2 * ‖a‖ + δ (i + 1) / 2 * ‖a‖ := add_le_add
      (norm_terminalCorrection_value_le h B (δ i) (hδ i) a)
      (norm_terminalCorrection_value_le h B (δ (i + 1)) (hδ (i + 1)) a)
    _ ≤ δ i * ‖a‖ := by nlinarith [norm_nonneg a]

theorem shell_error_partial_telescoping
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (a : B) (b : ℕ → B) (N : ℕ) :
    -terminalCorrection h B (δ 0) (hδ 0) a +
      (∑ i ∈ Finset.range N, terminalShell h B δ hδ i (a - b i)) =
    -terminalCorrection h B (δ N) (hδ N) a -
      ∑ i ∈ Finset.range N, terminalShell h B δ hδ i (b i) := by
  have ht := Finset.sum_range_sub' (fun i => terminalCorrection h B (δ i) (hδ i) a) N
  have htel : (∑ i ∈ Finset.range N, terminalShell h B δ hδ i a) =
      terminalCorrection h B (δ 0) (hδ 0) a - terminalCorrection h B (δ N) (hδ N) a := by
    exact ht
  simp only [map_sub, Finset.sum_sub_distrib]
  rw [htel]
  abel

theorem shellCoordinate_displacement_bound
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hstep : ∀ n, δ (n + 1) ≤ δ n / 4)
    (hlim : Tendsto δ atTop (𝓝 0))
    (f : C1History h B → B) (fm : ℕ → C1History h B → B)
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ i x, δ i * ‖fm i x‖ ≤ b i)
    (x : C1History h B)
    (hs : Summable (fun i => terminalShell h B δ hδ i (f x - fm i x))) :
    ‖historyInclusion h B (shellCoordinate h B δ hδ f fm x - x)‖ ≤ ∑' i, b i := by
  let v : ℕ → ContinuousHistory h B := fun i => historyInclusion h B (terminalShell h B δ hδ i (fm i x))
  have hvbound (i : ℕ) : ‖v i‖ ≤ b i :=
    (norm_terminalShell_value_le h B δ hδ hstep i (fm i x)).trans (hbound i x)
  have hvnorm : Summable (fun i => ‖v i‖) := hb.of_nonneg_of_le (fun i => norm_nonneg _) hvbound
  have hv : Summable v := hb.of_norm_bounded hvbound
  have hQlim : Tendsto (fun N => historyInclusion h B (terminalCorrection h B (δ N) (hδ N) (f x)))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun N => norm_terminalCorrection_value_le h B (δ N) (hδ N) (f x))
    simpa only [zero_div, zero_mul] using (hlim.div_const 2).mul_const ‖f x‖
  have hleft : Tendsto (fun N => historyInclusion h B
      (-terminalCorrection h B (δ 0) (hδ 0) (f x) +
        ∑ i ∈ Finset.range N, terminalShell h B δ hδ i (f x - fm i x)))
      atTop (𝓝 (historyInclusion h B (shellCoordinate h B δ hδ f fm x - x))) := by
    have heq : shellCoordinate h B δ hδ f fm x - x =
        -terminalCorrection h B (δ 0) (hδ 0) (f x) + terminalShellError h B δ hδ f fm x := by
      dsimp only [shellCoordinate]
      abel
    rw [heq]
    exact ((historyInclusion h B).continuous.tendsto _).comp
      (tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat)
  have hright : Tendsto (fun N => historyInclusion h B
      (-terminalCorrection h B (δ 0) (hδ 0) (f x) +
        ∑ i ∈ Finset.range N, terminalShell h B δ hδ i (f x - fm i x)))
      atTop (𝓝 (-∑' i, v i)) := by
    simp_rw [shell_error_partial_telescoping h B δ hδ (f x) (fun i => fm i x)]
    simp only [map_sub, map_neg, map_sum]
    simpa only [neg_zero, zero_sub, v] using hQlim.neg.sub hv.hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique hleft hright
  rw [heq, norm_neg]
  exact (norm_tsum_le_tsum_norm hvnorm).trans (hvnorm.tsum_le_tsum hvbound hb)

end

end GlobalRegularization
