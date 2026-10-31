import GlobalRegularization.HistorySpace

/-! A finite bounded-overlap estimate in the actual `C¹` history norm.
Both the value and derivative coordinates must vanish off the active
sets; an estimate on values alone would not suffice. -/

namespace GlobalRegularization

open scoped NNReal

noncomputable section

def boundedActiveIndices {ι X : Type*} (s : Finset ι) (active : ι → X → Prop) (t : X) : Finset ι := by
  classical
  exact s.filter (fun i => active i t)

theorem norm_map_sum_le_active_card
    {ι E B X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (s : Finset ι) (v : ι → E) (active : ι → X → Prop) (t : X)
    (L : E →L[ℝ] B) (hL : ∀ x, ‖L x‖ ≤ ‖x‖)
    (N : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcard : (boundedActiveIndices s active t).card ≤ N)
    (hzero : ∀ i ∈ s, ¬active i t → L (v i) = 0)
    (hbound : ∀ i ∈ s, ‖v i‖ ≤ M) :
    ‖L (∑ i ∈ s, v i)‖ ≤ (N : ℝ) * M := by
  classical
  have hsum : L (∑ i ∈ s, v i) = ∑ i ∈ boundedActiveIndices s active t, L (v i) := by
    rw [map_sum]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i his hin
    apply hzero i his
    simpa only [boundedActiveIndices, Finset.mem_filter, his, true_and] using hin
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ boundedActiveIndices s active t, ‖L (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ boundedActiveIndices s active t, M := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hL (v i)).trans (hbound i (Finset.mem_filter.mp hi).1)
    _ = ((boundedActiveIndices s active t).card : ℝ) * M := by simp
    _ ≤ (N : ℝ) * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM

variable {ι : Type*} (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem norm_history_sum_le_bounded_overlap
    (s : Finset ι) (v : ι → C1History h B) (active : ι → HistoryInterval h → Prop)
    (N : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcard : ∀ t, (boundedActiveIndices s active t).card ≤ N)
    (hzero : ∀ i ∈ s, ∀ t, ¬active i t →
      historyInclusion h B (v i) t = 0 ∧ historyDerivative h B (v i) t = 0)
    (hbound : ∀ i ∈ s, ‖v i‖ ≤ M) :
    ‖∑ i ∈ s, v i‖ ≤ (N : ℝ) * M := by
  change max ‖historyInclusion h B (∑ i ∈ s, v i)‖
    ‖historyDerivative h B (∑ i ∈ s, v i)‖ ≤ (N : ℝ) * M
  have hNM : 0 ≤ (N : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM
  apply max_le
  · apply (ContinuousMap.norm_le _ hNM).2
    intro t
    apply norm_map_sum_le_active_card s v active t
      ((ContinuousMap.evalCLM ℝ t).comp (historyInclusion h B)) _ N M hM (hcard t)
      (fun i hi hni => (hzero i hi t hni).1) hbound
    intro x
    exact ((historyInclusion h B x).norm_coe_le_norm t).trans (le_max_left ‖x.val.1‖ ‖x.val.2‖)
  · apply (ContinuousMap.norm_le _ hNM).2
    intro t
    apply norm_map_sum_le_active_card s v active t
      ((ContinuousMap.evalCLM ℝ t).comp (historyDerivative h B)) _ N M hM (hcard t)
      (fun i hi hni => (hzero i hi t hni).2) hbound
    intro x
    exact ((historyDerivative h B x).norm_coe_le_norm t).trans (le_max_right ‖x.val.1‖ ‖x.val.2‖)

end

end GlobalRegularization
