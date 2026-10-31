import GlobalRegularization.BoundaryScaling

/-! The actual shrinking terminal profiles have overlap at most two,
simultaneously for their values and derivatives. -/

namespace GlobalRegularization

open Filter
open scoped Topology

noncomputable section

theorem terminalProfile_eq_id_of_abs_lt (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : |t| < δ / 4) : terminalProfile δ hδ t = t := by
  have hb : terminalBump δ hδ t = 1 :=
    (terminalBump δ hδ).one_of_mem_closedBall (by simpa [terminalBump, Real.dist_eq] using ht.le)
  simp [terminalProfile, hb]

theorem terminalProfile_deriv_eq_one_of_abs_lt (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : |t| < δ / 4) : deriv (terminalProfile δ hδ) t = 1 := by
  have hb := (terminalBump δ hδ).eventuallyEq_one_of_mem_ball
    (by simpa [terminalBump, Real.dist_eq] using ht)
  have hq : terminalProfile δ hδ =ᶠ[𝓝 t] (fun s => s) :=
    hb.mono (fun s hs => by simp [terminalProfile, hs])
  exact ((hasDerivAt_id t).congr_of_eventuallyEq hq).deriv

theorem terminalProfile_eq_zero_of_abs_ge (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : δ / 2 ≤ |t|) : terminalProfile δ hδ t = 0 := by
  have hb := (terminalBump δ hδ).zero_of_le_dist
    (by simpa [terminalBump, Real.dist_eq] using ht)
  simp [terminalProfile, hb]

theorem terminalProfile_deriv_eq_zero_of_abs_gt (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : δ / 2 < |t|) : deriv (terminalProfile δ hδ) t = 0 := by
  have hevent : ∀ᶠ s in 𝓝 t, δ / 2 < |s| :=
    continuous_abs.continuousAt.eventually (Ioi_mem_nhds ht)
  have hq : terminalProfile δ hδ =ᶠ[𝓝 t] (fun _ => 0) :=
    hevent.mono (fun s hs => terminalProfile_eq_zero_of_abs_ge δ hδ hs.le)
  exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hq).deriv

def shellActive (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (i : ℕ) (t : ℝ) : Prop :=
  terminalProfile (δ i) (hδ i) t ≠ terminalProfile (δ (i + 1)) (hδ (i + 1)) t ∨
    deriv (terminalProfile (δ i) (hδ i)) t ≠ deriv (terminalProfile (δ (i + 1)) (hδ (i + 1))) t

instance shellActive_decidable (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (t : ℝ) :
    DecidablePred (fun i => shellActive δ hδ i t) := fun _ => Classical.propDecidable _

theorem shrinkingWidths_antitone (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hstep : ∀ n, δ (n + 1) ≤ δ n / 4) : Antitone δ := by
  apply antitone_nat_of_succ_le
  intro n
  have hs := hstep n
  have hp := hδ n
  linarith

theorem shellActive_annulus (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hstep : ∀ n, δ (n + 1) ≤ δ n / 4) {i : ℕ} {t : ℝ}
    (ht : shellActive δ hδ i t) : δ (i + 1) / 4 ≤ |t| ∧ |t| ≤ δ i / 2 := by
  have hmono : δ (i + 1) ≤ δ i := shrinkingWidths_antitone δ hδ hstep (by omega)
  constructor
  · by_contra hlow
    have hinner₁ : |t| < δ (i + 1) / 4 := lt_of_not_ge hlow
    have hinner₀ : |t| < δ i / 4 := by linarith
    rcases ht with hv | hd
    · exact hv (by rw [terminalProfile_eq_id_of_abs_lt _ _ hinner₀,
        terminalProfile_eq_id_of_abs_lt _ _ hinner₁])
    · exact hd (by rw [terminalProfile_deriv_eq_one_of_abs_lt _ _ hinner₀,
        terminalProfile_deriv_eq_one_of_abs_lt _ _ hinner₁])
  · by_contra hhigh
    have houter₀ : δ i / 2 < |t| := lt_of_not_ge hhigh
    have houter₁ : δ (i + 1) / 2 < |t| := by linarith
    rcases ht with hv | hd
    · exact hv (by rw [terminalProfile_eq_zero_of_abs_ge _ _ houter₀.le,
        terminalProfile_eq_zero_of_abs_ge _ _ houter₁.le])
    · exact hd (by rw [terminalProfile_deriv_eq_zero_of_abs_gt _ _ houter₀,
        terminalProfile_deriv_eq_zero_of_abs_gt _ _ houter₁])

theorem shellActive_not_far (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hstep : ∀ n, δ (n + 1) ≤ δ n / 4) {i j : ℕ} {t : ℝ}
    (hi : shellActive δ hδ i t) (hj : shellActive δ hδ j t) : j ≤ i + 1 := by
  by_contra hij
  have hlarge : i + 2 ≤ j := by omega
  have hdj : δ j ≤ δ (i + 2) := shrinkingWidths_antitone δ hδ hstep hlarge
  have hs := hstep (i + 1)
  have hbi := (shellActive_annulus δ hδ hstep hi).1
  have hbj := (shellActive_annulus δ hδ hstep hj).2
  have hp := hδ (i + 1)
  linarith

theorem shellActive_card_le_two (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hstep : ∀ n, δ (n + 1) ≤ δ n / 4) (s : Finset ℕ) (t : ℝ) :
    (s.filter (fun i => shellActive δ hδ i t)).card ≤ 2 := by
  classical
  let a := s.filter (fun i => shellActive δ hδ i t)
  by_cases ha : a.Nonempty
  · let i := a.min' ha
    have himem : i ∈ a := a.min'_mem ha
    have hsub : a ⊆ {i, i + 1} := by
      intro j hj
      have hij : i ≤ j := a.min'_le j hj
      have hiA : shellActive δ hδ i t := (Finset.mem_filter.mp himem).2
      have hjA : shellActive δ hδ j t := (Finset.mem_filter.mp hj).2
      have hji := shellActive_not_far δ hδ hstep hiA hjA
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcard : ({i, i + 1} : Finset ℕ).card ≤ 2 := by simp
    exact (Finset.card_le_card hsub).trans hcard
  · have hempty : a = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    change a.card ≤ 2
    rw [hempty]
    simp

end

end GlobalRegularization
