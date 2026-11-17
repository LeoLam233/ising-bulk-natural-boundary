import IsingBulk.AnisoF002.C03.RegularModelCenteredEstimates
import IsingBulk.AnisoF002.C03.NegativeActualStepBound
import IsingBulk.AnisoF002.C03.NegativeSelectionGates

/-!
# Integer Taylor-order selection for the actual first-winding model

The endpoint signs and one-step recurrence are now applied to the literal
full complex model.  Every analytic-factor, gamma-range, nonzero-factor,
rounding and step-size gate is discharged.  The selected order is an
integer with actual neighboring-index discrepancy O(1/N).
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem exists_actual_model_integer_crossing {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c : ℝ) {s : ℝ} (hs : 0 < s)
    (d : ℕ) (hd : Even d) (hdpos : 0 < d) :
    ∃ K R : ℝ, 0 < K ∧ 0 < R ∧ ∀ n : ℕ, Odd n → R ≤ (n : ℝ) + d →
      ∃ j : ℕ, selectionStart (n + d) < j ∧ j ≤ selectionFinish (n + d) ∧
        0 ≤ actualModelCrossing B c s n d j ∧
        actualModelCrossing B c s n d j ≤ K / ((n : ℝ) + d) ∧
        ((n : ℝ) + d) ^ 2 * Real.log ((n : ℝ) + d) / 3 ≤ (j : ℝ) ∧
        (j : ℝ) ≤ 3 * ((n : ℝ) + d) ^ 2 * Real.log ((n : ℝ) + d) / 2 := by
  obtain ⟨C, Rc, hC, hRc, hmodel⟩ := actual_model_centered_estimates hB hslit c hs d hd hdpos
  obtain ⟨K, Rs, hK, hRs, hstep⟩ := exists_actual_order_step_upper_bound hB hslit c hs
  let T : ℝ := max 256 (32 * (C + 1))
  let R : ℝ := max Rc (max Rs (max (4 * (d : ℝ) + 1) (Real.exp T)))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  refine ⟨K * d, R, mul_pos hK hdR, hRc.trans_le (le_max_left _ _), ?_⟩
  intro n hn hlarge
  have hnpos := hn.pos
  have hcenter : 1 ≤ n + d := by omega
  have hx : 0 < (n : ℝ) + d := by positivity
  have hRc' : Rc ≤ (n : ℝ) + d := (le_max_left _ _).trans hlarge
  have hRs' : Rs ≤ (n : ℝ) + d :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hfour : 4 * (d : ℝ) + 1 ≤ (n : ℝ) + d :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hExp : Real.exp T ≤ (n : ℝ) + d :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hT : T ≤ Real.log ((n : ℝ) + d) := (Real.le_log_iff_exp_le hx).mpr hExp
  have ht : 256 ≤ Real.log ((n + d : ℕ) : ℝ) := by
    simpa only [Nat.cast_add] using (le_max_left _ _).trans hT
  have hClog : 32 * (C + 1) ≤ Real.log ((n + d : ℕ) : ℝ) := by
    simpa only [Nat.cast_add] using (le_max_right _ _).trans hT
  have hdsmall : (d : ℝ) ≤ ((n : ℝ) + d) / 4 := by linarith
  have hgamma (j : ℕ) (hj : selectionStart (n + d) ≤ j) :
      2 * (particleExponent (n + 2 * d) : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast integer_interval_gamma_range hcenter ht hj
  have hsf := (selection_integer_endpoint_bounds hcenter ht).2.2.2.2
  have hstart := (hmodel n (selectionStart (n + d)) hn hRc' (hgamma _ le_rfl)).1
  have hfinish := (hmodel n (selectionFinish (n + d)) hn hRc' (hgamma _ hsf)).1
  have hsteps : ∀ j : ℕ, selectionStart (n + d) ≤ j → j < selectionFinish (n + d) →
      actualModelCrossing B c s n d (j + 1) - actualModelCrossing B c s n d j ≤
        K * (d : ℝ) / ((n : ℝ) + d) := by
    intro j hj _
    have hjα : particleExponent (n + 2 * d) ≤ j := by
      have hh := integer_interval_gamma_range hcenter ht hj
      omega
    exact hstep n d hn hd hRs' hdsmall j hjα
  obtain ⟨j, hjlo, hjhi, hj0, hjδ, hjlower, hjupper⟩ :=
    exists_integer_window_crossing (actualModelCrossing B c s n d)
      hcenter ht hC.le hdR hClog
      (by simpa only [actualModelCrossing, Nat.cast_add] using hstart)
      (by simpa only [actualModelCrossing, Nat.cast_add] using hfinish) hsteps
  refine ⟨j, hjlo, hjhi, hj0, hjδ, ?_, ?_⟩
  · simpa only [Nat.cast_add] using hjlower
  · simpa only [Nat.cast_add] using hjupper

end
end IsingBulk.AnisoF002.NegativeHT
