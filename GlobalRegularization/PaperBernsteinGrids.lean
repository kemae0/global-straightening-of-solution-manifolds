import GlobalRegularization.BernsteinHistoryRanges
import GlobalRegularization.UnitHistoryOperatorNorm

/-! The manuscript's actual Bernstein operators of degrees 4^m, including
nestedness stated for the operators themselves and their Hilbert ranges. -/

namespace GlobalRegularization

open Set Filter
open scoped unitInterval NNReal Topology

noncomputable section

def paperBernsteinIndex (m : ℕ) : ℕ := 4 ^ m - 1

theorem paperBernsteinIndex_add_one (m : ℕ) : paperBernsteinIndex m + 1 = 4 ^ m := by
  have hp : 0 < (4 : ℕ) ^ m := by positivity
  unfold paperBernsteinIndex
  omega

theorem paperBernsteinIndex_ge (m : ℕ) : m ≤ paperBernsteinIndex m := by
  have hpow : m + 1 ≤ (4 : ℕ) ^ m := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ]; nlinarith
  unfold paperBernsteinIndex
  omega

theorem paperBernsteinIndex_tendsto : Tendsto paperBernsteinIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  exact eventually_atTop.mpr ⟨N, fun m hm => hm.trans (paperBernsteinIndex_ge m)⟩

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def paperBernstein (m : ℕ) : C1History 1 B →L[ℝ] C1History 1 B :=
  unitHistoryBernsteinCLM B (paperBernsteinIndex m)

theorem paperBernstein_contraction (m : ℕ) : ‖paperBernstein B m‖ ≤ 1 :=
  norm_unitHistoryBernsteinCLM_le B _

theorem paperBernstein_strong (x : C1History 1 B) :
    Tendsto (fun m => paperBernstein B m x) atTop (𝓝 x) :=
  (unitHistoryBernstein_strong B x).comp paperBernsteinIndex_tendsto

theorem paperBernstein_continuous_operator_limit :
    Tendsto (fun m => (historyInclusion 1 B).comp (paperBernstein B m) - historyInclusion 1 B)
      atTop (𝓝 0) :=
  (unitHistoryBernstein_operator_tendsto_zero B).comp paperBernsteinIndex_tendsto

theorem paperBernstein_samples_nested (i j : ℕ) (hij : i ≤ j) (x y : C1History 1 B)
    (hxy : unitHistorySamples B (paperBernsteinIndex j) x = unitHistorySamples B (paperBernsteinIndex j) y) :
    unitHistorySamples B (paperBernsteinIndex i) x = unitHistorySamples B (paperBernsteinIndex i) y := by
  ext k
  let q : ℕ := 4 ^ (j - i)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hdeg : (4 : ℕ) ^ j = 4 ^ i * q := by
    dsimp only [q]
    rw [← pow_add]
    congr 1
    omega
  have hki : (k : ℕ) ≤ 4 ^ i := by
    have hk := k.isLt
    have hi := paperBernsteinIndex_add_one i
    omega
  let l : Fin (paperBernsteinIndex j + 2) := ⟨(k : ℕ) * q, by
    have hm := Nat.mul_le_mul_right q hki
    rw [← hdeg] at hm
    have hj := paperBernsteinIndex_add_one j
    omega⟩
  have hnode : unitHistoryNode (paperBernsteinIndex j) l = unitHistoryNode (paperBernsteinIndex i) k := by
    apply Subtype.ext
    simp only [unitHistoryNode, bernstein.z, Nat.cast_add, Nat.cast_one]
    have hiR : (paperBernsteinIndex i : ℝ) + 1 = ((4 : ℕ) ^ i : ℝ) := by
      exact_mod_cast paperBernsteinIndex_add_one i
    have hjR : (paperBernsteinIndex j : ℝ) + 1 = ((4 : ℕ) ^ j : ℝ) := by
      exact_mod_cast paperBernsteinIndex_add_one j
    have hlR : (l : ℝ) = (k : ℝ) * (q : ℝ) := by dsimp only [l]; push_cast; rfl
    have hdR : (4 : ℝ) ^ j = (4 : ℝ) ^ i * (q : ℝ) := by exact_mod_cast hdeg
    rw [hiR, hjR, hlR]
    norm_num only [Nat.cast_ofNat]
    rw [hdR]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hi0 : (4 : ℝ) ^ i ≠ 0 := by positivity
    field_simp
  have he := congrArg (fun a : Fin (paperBernsteinIndex j + 2) → B => a l) hxy
  simpa only [unitHistorySamples_apply, hnode] using he

theorem paperBernstein_nested (i j : ℕ) (hij : i ≤ j) (x y : C1History 1 B)
    (hxy : paperBernstein B j x = paperBernstein B j y) : paperBernstein B i x = paperBernstein B i y := by
  apply (unitHistoryBernstein_eq_iff_samples B (paperBernsteinIndex i) x y).mpr
  exact paperBernstein_samples_nested B i j hij x y
    ((unitHistoryBernstein_eq_iff_samples B (paperBernsteinIndex j) x y).mp hxy)

theorem paperBernstein_separates (x y : C1History 1 B)
    (hxy : ∀ m, paperBernstein B m x = paperBernstein B m y) : x = y :=
  tendsto_nhds_unique (paperBernstein_strong B x)
    ((tendsto_congr hxy).mpr (paperBernstein_strong B y))

theorem paperBernstein_terminal_invisible (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hshort : δ / 2 < 1 / (4 : ℝ) ^ m) :
    (paperBernstein B m).comp (terminalCorrection 1 B δ hδ) = 0 := by
  apply unitHistoryBernstein_annihilates_terminal B (paperBernsteinIndex m) δ hδ
  have hdeg : (paperBernsteinIndex m : ℝ) + 1 = (4 : ℝ) ^ m := by
    exact_mod_cast paperBernsteinIndex_add_one m
  simpa only [hdeg] using hshort

theorem paperBernstein_width_antitone : Antitone (fun m : ℕ => 1 / (4 : ℝ) ^ m) := by
  intro m n hmn
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hmn)

def paperBernsteinRangeEquiv (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (m : ℕ) :
    HilbertHistoryObservationSpace H (paperBernsteinIndex m) ≃L[ℝ] LinearMap.range (paperBernstein H m) :=
  hilbertBernsteinRangeEquiv H (paperBernsteinIndex m)

end

end GlobalRegularization
