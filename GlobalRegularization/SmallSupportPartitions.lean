import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Basic

/-! Actual finite continuous partitions of unity whose nonzero supports
have arbitrarily small diameter, obtained from a finite ball cover. -/

namespace GlobalRegularization

open Set Metric

noncomputable section

universe u

structure SmallSupportPartition (X : Type u) [MetricSpace X] (r : ℝ) where
  index : Type u
  [finiteIndex : Fintype index]
  weight : index → C(X, ℝ)
  nonneg : ∀ j x, 0 ≤ weight j x
  sum_one : ∀ x, ∑ j, weight j x = 1
  support_close : ∀ j x y, weight j x ≠ 0 → weight j y ≠ 0 → dist x y < r

attribute [instance] SmallSupportPartition.finiteIndex

theorem exists_smallSupportPartition (X : Type u) [MetricSpace X] [CompactSpace X]
    (r : ℝ) (hr : 0 < r) : Nonempty (SmallSupportPartition X r) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ball x (r / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, mem_ball_self (by positivity)⟩)
  have hcover : (univ : Set X) ⊆ ⋃ j : s, ball (j : X) (r / 2) := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hjs, hxj⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨⟨j, hjs⟩, hxj⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun j : s => ball (j : X) (r / 2)) (fun _ => isOpen_ball) hcover
  refine ⟨{ index := s, weight := ρ, nonneg := ρ.nonneg, sum_one := ?_, support_close := ?_ }⟩
  · intro x
    exact ρ.sum_finsupport' (mem_univ x) (Finset.subset_univ _)
  · intro j x y hx hy
    have hxball := hρ j (subset_closure hx)
    have hyball := hρ j (subset_closure hy)
    have hd := dist_triangle x (j : X) y
    have hx' : dist x (j : X) < r / 2 := hxball
    have hy' : dist (j : X) y < r / 2 := by simpa only [dist_comm] using hyball
    linarith

def smallSupportPartition (X : Type u) [MetricSpace X] [CompactSpace X]
    (r : ℝ) (hr : 0 < r) : SmallSupportPartition X r :=
  (exists_smallSupportPartition X r hr).some

end

end GlobalRegularization
