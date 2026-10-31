import GlobalRegularization.ShellGeometry

/-! The actual terminal cutoff `Vσ g(t) = g(min(t,-σ))`, its contraction
bound, strong convergence, and annihilation of short correction derivatives. -/

namespace GlobalRegularization

open Set Filter Metric
open scoped NNReal Topology

noncomputable section

def terminalPastPoint (h : ℝ≥0) (σ : ℝ) (hσh : σ ≤ (h : ℝ)) (t : HistoryInterval h) :
    HistoryInterval h :=
  ⟨min (t : ℝ) (-σ), le_min t.property.1 (neg_le_neg hσh),
    (min_le_left _ _).trans t.property.2⟩

theorem terminalPastPoint_dist_le (h : ℝ≥0) (σ : ℝ) (hσ : 0 ≤ σ) (hσh : σ ≤ (h : ℝ))
    (t : HistoryInterval h) : dist (terminalPastPoint h σ hσh t : ℝ) (t : ℝ) ≤ σ := by
  by_cases ht : (t : ℝ) ≤ -σ
  · simp only [terminalPastPoint, min_eq_left ht, dist_self]
    exact hσ
  · have ht' : -σ ≤ (t : ℝ) := (lt_of_not_ge ht).le
    simp only [terminalPastPoint, min_eq_right ht', Real.dist_eq]
    rw [abs_of_nonpos (by linarith)]
    linarith [t.property.2]

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def terminalHistoryCutoffL (σ : ℝ) (hσh : σ ≤ (h : ℝ)) : ContinuousHistory h B →ₗ[ℝ] ContinuousHistory h B where
  toFun g := ⟨fun t => g (terminalPastPoint h σ hσh t), by
    apply g.continuous.comp
    exact (continuous_subtype_val.min continuous_const).subtype_mk _⟩
  map_add' g j := by ext t; rfl
  map_smul' c g := by ext t; rfl

def terminalHistoryCutoff (σ : ℝ) (hσh : σ ≤ (h : ℝ)) : ContinuousHistory h B →L[ℝ] ContinuousHistory h B :=
  (terminalHistoryCutoffL h B σ hσh).mkContinuous 1 (by
    intro g
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg g)).2
    intro t
    exact g.norm_coe_le_norm _)

omit [CompleteSpace B] in
theorem norm_terminalHistoryCutoff_le (σ : ℝ) (hσh : σ ≤ (h : ℝ)) :
    ‖terminalHistoryCutoff h B σ hσh‖ ≤ 1 :=
  (terminalHistoryCutoffL h B σ hσh).mkContinuous_norm_le zero_le_one _

omit [CompleteSpace B] in
theorem terminalHistoryCutoff_strong
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hσh : ∀ n, σ n ≤ (h : ℝ))
    (hlim : Tendsto σ atTop (𝓝 0)) (g : ContinuousHistory h B) :
    Tendsto (fun n => terminalHistoryCutoff h B (σ n) (hσh n) g) atTop (𝓝 g) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨η, hη, hnear⟩ := Metric.uniformContinuous_iff.mp
    (uniformContinuous_extendHistory h B g) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim η hη
  refine ⟨N, fun n hn => ?_⟩
  have hs : σ n < η := by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (hσ n)] using hN n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have hdist := (terminalPastPoint_dist_le h (σ n) (hσ n) (hσh n) t).trans_lt hs
  have ht := hnear hdist
  rw [extendHistory_coe h B g (terminalPastPoint h (σ n) (hσh n) t), extendHistory_coe h B g t] at ht
  have ht' : ‖g (terminalPastPoint h (σ n) (hσh n) t) - g t‖ < ε / 2 := by
    simpa only [dist_eq_norm] using ht
  exact ht'.le

theorem terminalHistoryCutoff_annihilates_terminal_derivative
    (σ : ℝ) (hσh : σ ≤ (h : ℝ)) (δ : ℝ) (hδ : 0 < δ) (hshort : δ / 2 < σ) :
    (terminalHistoryCutoff h B σ hσh).comp
      ((historyDerivative h B).comp (terminalCorrection h B δ hδ)) = 0 := by
  apply ContinuousLinearMap.ext
  intro a
  ext t
  change deriv (terminalProfile δ hδ) (terminalPastPoint h σ hσh t) • a = 0
  have ht : (terminalPastPoint h σ hσh t : ℝ) ≤ -σ := min_le_right _ _
  have ha : δ / 2 < |(terminalPastPoint h σ hσh t : ℝ)| := by
    have hb := neg_le_abs (terminalPastPoint h σ hσh t : ℝ)
    linarith
  rw [terminalProfile_deriv_eq_zero_of_abs_gt δ hδ ha, zero_smul]

end

end GlobalRegularization
