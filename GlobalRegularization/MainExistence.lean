import GlobalRegularization.NormalizedLocalized
import GlobalRegularization.HistoryRescaleEquiv
import GlobalRegularization.ExtendedDerivativeTransport
import GlobalRegularization.LocalizedTransport

/-! The principal spatial existence theorem under property (e), on the
actual history space for every positive history length. -/

namespace GlobalRegularization

open Set
open scoped NNReal Topology

noncomputable section

variable (h : ℝ≥0) (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B]

theorem property_e_localized_straightening_with_isotopy
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ chart : LocalizedHistoryStraightening h B U f τ ε,
      chart.toC1Straightening.HasAffineIsotopy := by
  let R := historyRescaleEquiv h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  let T : C1History 1 B →L[ℝ] C1History h B := R.symm
  have hInv : (h : ℝ)⁻¹ * (h : ℝ) = 1 := inv_mul_cancel₀ hh.ne'
  let S := continuousHistoryRescaleCLM 1 h B (h : ℝ)⁻¹ (inv_nonneg.mpr hh.le) hInv
  let P : B →L[ℝ] B := (h : ℝ) • ContinuousLinearMap.id ℝ B
  have hcomm : (historyInclusion h B).comp T = S.comp (historyInclusion 1 B) :=
    historyRescaleEquiv_symm_inclusion h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  let g : C1History 1 B → B := fun x => P (f (T x))
  have hU₁ : IsOpen (R.symm ⁻¹' U) := hU.preimage R.symm.continuous
  have he₁ : HasExtendedDerivative (R.symm ⁻¹' U) (historyInclusion 1 B) g :=
    he.linear_pullback hU T S P hcomm
  obtain ⟨s, hiso⟩ := property_e_normalized_localized_straightening_with_isotopy B (R.symm ⁻¹' U) hU₁ g he₁
    (τ / (h : ℝ)) ε (div_pos hτ hh) hε
  let q := historyScaleTime 1 h (h : ℝ)⁻¹ (inv_nonneg.mpr hh.le) hInv
  have hval : ∀ y t, historyInclusion h B (R.symm y) t = historyInclusion 1 B y (q t) :=
    historyRescaleEquiv_symm_value h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  have hzero : q (historyRight h) = historyRight 1 := by
    apply Subtype.ext
    simp only [q, historyScaleTime, historyRight, mul_zero]
  have hremote : ∀ t : HistoryInterval h, (t : ℝ) ≤ -τ → (q t : ℝ) ≤ -(τ / (h : ℝ)) := by
    intro t ht
    have hm := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hh.le)
    simpa only [q, historyScaleTime, mul_neg, div_eq_mul_inv, mul_comm] using hm
  have hD : ∀ y, endpointDerivative h B (R.symm y) = (h : ℝ)⁻¹ • endpointDerivative 1 B y :=
    historyRescaleEquiv_symm_endpoint h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  have hg : ∀ x, (h : ℝ)⁻¹ • g (R x) = f x := by
    intro x
    change (h : ℝ)⁻¹ • ((h : ℝ) • f (R.symm (R x))) = f x
    rw [R.symm_apply_apply, inv_smul_smul₀ hh.ne']
  have hnorm : ∀ z, ‖historyInclusion h B (R.symm z)‖ ≤ ‖historyInclusion 1 B z‖ :=
    norm_historyRescaleEquiv_symm_value_le h 1 B hh (by norm_num) (h : ℝ) hh (by simp)
  exact ⟨localizedStraightening_time_transport h B R q U f g τ (τ / (h : ℝ)) ε (h : ℝ)⁻¹
    hval hzero hremote hD hg hnorm s,
    localizedStraightening_time_transport_isotopy h B R q U f g τ (τ / (h : ℝ)) ε (h : ℝ)⁻¹
      hval hzero hremote hD hg hnorm s hiso⟩

theorem property_e_localized_straightening
    (hh : 0 < (h : ℝ)) (U : Set (C1History h B)) (hU : IsOpen U) (f : C1History h B → B)
    (he : HasExtendedDerivative U (historyInclusion h B) f)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    Nonempty (LocalizedHistoryStraightening h B U f τ ε) := by
  obtain ⟨chart, hisotopy⟩ := property_e_localized_straightening_with_isotopy h B hh U hU f he τ ε hτ hε
  exact ⟨chart⟩
/-- The concrete finite-dimensional principal claim is now derived from
its assumptions, with no added existence hypothesis. -/
theorem mainClaim (n : ℕ) : MainClaim n := by
  intro h hh U f hU he τ ε hτ hτh hε
  exact property_e_localized_straightening h (Fin n → ℝ) hh U hU f he τ ε hτ hε

end

end GlobalRegularization
