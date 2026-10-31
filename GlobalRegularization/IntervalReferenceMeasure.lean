import GlobalRegularization.AdaptedHistoryOperators
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! A genuine finite full-support measure on the history interval, with
zero mass at the present endpoint: the pullback of Lebesgue measure. -/

namespace GlobalRegularization

open Set MeasureTheory Metric
open scoped NNReal

noncomputable section

def historyLebesgue (h : ℝ≥0) : Measure (HistoryInterval h) :=
  volume.comap (fun t : HistoryInterval h => (t : ℝ))

theorem historyInterval_measurableEmbedding (h : ℝ≥0) :
    MeasurableEmbedding (fun t : HistoryInterval h => (t : ℝ)) :=
  (show Topology.IsClosedEmbedding (fun t : HistoryInterval h => (t : ℝ)) from
    isClosed_Icc.isClosedEmbedding_subtypeVal).measurableEmbedding

theorem historyLebesgue_apply (h : ℝ≥0) (s : Set (HistoryInterval h)) :
    historyLebesgue h s = volume ((fun t : HistoryInterval h => (t : ℝ)) '' s) :=
  (historyInterval_measurableEmbedding h).comap_apply _ _

instance (h : ℝ≥0) : IsFiniteMeasure (historyLebesgue h) := by
  constructor
  rw [historyLebesgue_apply]
  have heq : ((fun t : HistoryInterval h => (t : ℝ)) '' univ) = Icc (-(h : ℝ)) 0 := by
    ext t
    simp [HistoryInterval]
  rw [heq, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem historyLebesgue_singleton (h : ℝ≥0) (a : HistoryInterval h) : historyLebesgue h {a} = 0 := by
  rw [historyLebesgue_apply, image_singleton]
  exact measure_singleton (a : ℝ)

theorem historyLebesgue_full_support (h : ℝ≥0) (hh : 0 < (h : ℝ)) :
    ∀ U : Set (HistoryInterval h), IsOpen U → U.Nonempty → 0 < historyLebesgue h U := by
  intro U hU hne
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO (x : ℝ) hx
  let a := max (-(h : ℝ)) ((x : ℝ) - r / 2)
  let b := min 0 ((x : ℝ) + r / 2)
  have hab : a < b := by
    dsimp only [a, b]
    rw [lt_min_iff, max_lt_iff, max_lt_iff]
    constructor
    · constructor <;> linarith [x.property.2]
    · constructor <;> linarith [x.property.1]
  have hsub : Ioo a b ⊆ (fun t : HistoryInterval h => (t : ℝ)) ''
      ((fun t : HistoryInterval h => (t : ℝ)) ⁻¹' O) := by
    intro y hy
    have hya : -(h : ℝ) ≤ y := (le_max_left _ _).trans hy.1.le
    have hyb : y ≤ 0 := hy.2.le.trans (min_le_left _ _)
    refine ⟨⟨y, hya, hyb⟩, ?_, rfl⟩
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    have hlo := (le_max_right (-(h : ℝ)) ((x : ℝ) - r / 2)).trans_lt hy.1
    have hhi := hy.2.trans_le (min_le_right 0 ((x : ℝ) + r / 2))
    constructor <;> linarith
  rw [historyLebesgue_apply]
  have hp : 0 < volume (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact hp.trans_le (measure_mono hsub)

end

end GlobalRegularization
