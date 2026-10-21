import IsingBulk.HT.Final.FullFarIdentification
import IsingBulk.HT.Final.FullChartNormal

/-! Four-chart gluing of the literal odd full-site coefficients. The left
chart is a separately constructed source integral, not an even reflection. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

def exteriorOddTerm (n : ℕ) (s : ℂ) : ℂ :=
  if 0 < (sourceS s).im then upperFullCoefficient (2*n+1) s
  else if (sourceS s).im < 0 then star (upperFullCoefficient (2*n+1) (star s))
  else if 2 < (sourceS s).re then rightFullCoefficient (2*n+1) s
  else leftFullCoefficient (2*n+1) s

theorem exteriorOddTerm_eq_upper (n : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    exteriorOddTerm n s = upperFullCoefficient (2*n+1) s := by
  simp [exteriorOddTerm,hs]

theorem exteriorOddTerm_eq_lower (n : ℕ) {s : ℂ} (hs : (sourceS s).im < 0) :
    exteriorOddTerm n s = star (upperFullCoefficient (2*n+1) (star s)) := by
  simp [exteriorOddTerm,hs,not_lt.mpr hs.le]

theorem exteriorOddTerm_eq_right (n : ℕ) {s : ℂ} (hs : 2 < (sourceS s).re) :
    exteriorOddTerm n s = rightFullCoefficient (2*n+1) s := by
  by_cases hu : 0 < (sourceS s).im
  · rw [exteriorOddTerm_eq_upper n hu]
    exact (rightFullCoefficient_eq_upper _ (by omega) hs hu).symm
  · by_cases hl : (sourceS s).im < 0
    · rw [exteriorOddTerm_eq_lower n hl]
      have hsc : 2 < (sourceS (star s)).re := by simpa [sourceS_conj_map] using hs
      have hic : 0 < (sourceS (star s)).im := by simpa [sourceS_conj_map] using neg_pos.mpr hl
      rw [← rightFullCoefficient_eq_upper _ (by omega) hsc hic,
        rightFullCoefficient_conjugate,star_star]
    · simp [exteriorOddTerm,hu,hl,hs]

theorem exteriorOddTerm_eq_left (n : ℕ) {s : ℂ} (hs : (sourceS s).re < -2) :
    exteriorOddTerm n s = leftFullCoefficient (2*n+1) s := by
  by_cases hu : 0 < (sourceS s).im
  · rw [exteriorOddTerm_eq_upper n hu]
    exact (leftFullCoefficient_eq_upper _ (by omega) hs hu).symm
  · by_cases hl : (sourceS s).im < 0
    · rw [exteriorOddTerm_eq_lower n hl]
      have hsc : (sourceS (star s)).re < -2 := by simpa [sourceS_conj_map] using hs
      have hic : 0 < (sourceS (star s)).im := by simpa [sourceS_conj_map] using neg_pos.mpr hl
      rw [← leftFullCoefficient_eq_upper _ (by omega) hsc hic,
        leftFullCoefficient_conjugate,star_star]
    · have hnr : ¬ 2 < (sourceS s).re := by linarith
      simp [exteriorOddTerm,hu,hl,hnr]

theorem exteriorOddTerm_analyticAt (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticAt ℂ (exteriorOddTerm n) s := by
  rcases exterior_trace_charts hs with hu | hl | hr | hL
  · apply (upperFullCoefficient_analyticAt (2*n+1) (by omega) hu).congr
    filter_upwards [upperTraceDomain_isOpen.mem_nhds hu] with t ht
    exact (exteriorOddTerm_eq_upper n ht).symm
  · have hc : 0 < (sourceS (star s)).im := by simpa [sourceS_conj_map] using neg_pos.mpr hl
    apply (analyticAt_conjugate_reflection
      (upperFullCoefficient_analyticAt (2*n+1) (by omega) hc)).congr
    filter_upwards [lowerTraceDomain_isOpen.mem_nhds hl] with t ht
    exact (exteriorOddTerm_eq_lower n ht).symm
  · apply (rightFullCoefficient_analyticAt (2*n+1) (by omega) hr).congr
    filter_upwards [rightTraceDomain_isOpen.mem_nhds hr] with t ht
    exact (exteriorOddTerm_eq_right n ht).symm
  · apply (leftFullCoefficient_analyticAt (2*n+1) (by omega) hL).congr
    filter_upwards [leftTraceDomain_isOpen.mem_nhds hL] with t ht
    exact (exteriorOddTerm_eq_left n ht).symm

/-- The glued coefficients retain their exact full-site source germ. -/
theorem exteriorOddTerm_eq_quarter_far (n : ℕ) {s : ℂ} (hs : 16 < ‖s‖) :
    exteriorOddTerm n s = standardFormFactor (2*n+1) (1/4) s := by
  rcases exterior_trace_charts (show 1 < ‖s‖ by linarith) with hu | hl | hr | hL
  · rw [exteriorOddTerm_eq_upper n hu]
    exact upperFullCoefficient_eq_quarter_far _ (by omega) hu hs
  · have hc : 0 < (sourceS (star s)).im := by simpa using neg_pos.mpr hl
    rw [exteriorOddTerm_eq_lower n hl,
      upperFullCoefficient_eq_quarter_far _ (by omega) hc (by simpa using hs),
      standardFormFactor_conjugate,star_star]
  · rw [exteriorOddTerm_eq_right n hr]
    exact rightFullCoefficient_eq_quarter_far _ (by omega) hr hs
  · rw [exteriorOddTerm_eq_left n hL]
    exact leftFullCoefficient_eq_quarter_far _ (by omega) hL hs

/-- Schwarz reflection follows from actual source conjugation on each
chart, including the negative real chart. -/
theorem exteriorOddTerm_conjugate (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    exteriorOddTerm n (star s) = star (exteriorOddTerm n s) := by
  rcases exterior_trace_charts hs with hu | hl | hr | hL
  · have hc : (sourceS (star s)).im < 0 := by simpa using neg_neg_of_pos hu
    rw [exteriorOddTerm_eq_lower n hc,star_star,exteriorOddTerm_eq_upper n hu]
  · have hc : 0 < (sourceS (star s)).im := by simpa using neg_pos.mpr hl
    rw [exteriorOddTerm_eq_upper n hc,exteriorOddTerm_eq_lower n hl,star_star]
  · have hc : 2 < (sourceS (star s)).re := by simpa using hr
    rw [exteriorOddTerm_eq_right n hc,exteriorOddTerm_eq_right n hr,rightFullCoefficient_conjugate]
  · have hc : (sourceS (star s)).re < -2 := by simpa using hL
    rw [exteriorOddTerm_eq_left n hc,exteriorOddTerm_eq_left n hL,leftFullCoefficient_conjugate]

end
end IsingBulk.HT.Final
