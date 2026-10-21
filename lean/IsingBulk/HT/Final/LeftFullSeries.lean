import IsingBulk.HT.Final.UpperFullSeries
import IsingBulk.HT.Final.LeftOnsiteSeries
import IsingBulk.HT.Final.LeftOffsiteSeries

/-! The actual full-site odd series on the left-trace chart. Both onsite
and offsite normal convergence are constructed before summing. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail Set Filter Metric
open scoped Topology BigOperators

def leftFullCoefficient (N : ℕ) (s : ℂ) : ℂ :=
  leftOnsiteFormFactor N s + 2*leftFormFactor N s

def leftFullOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, leftFullCoefficient (2*n+1) s

theorem leftFullCoefficient_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    leftFullCoefficient N s = standardFormFactor N r s := by
  rw [leftFullCoefficient, leftOnsiteFormFactor_eq_fixed_radius N hN hr hr1 hm,
    leftFormFactor_eq_fixed_radius N hN hr hr1 hm]
  exact (standardFormFactor_eq_onsite_add_double N hN r s (leftRoot s)
    (leftRoot_admissible hr hr1 hm)).symm

theorem leftFullCoefficient_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : (sourceS s).re < -2) : AnalyticAt ℂ (leftFullCoefficient N) s :=
  (leftOnsiteFormFactor_analyticAt N hN hs).add
    ((analyticAt_const (v := (2:ℂ))).mul (leftFormFactor_analyticAt N hN hs))

theorem leftFullCoefficient_iteratedDeriv (N : ℕ) (hN : 0 < N) (j : ℕ) {s : ℂ}
    (hs : (sourceS s).re < -2) :
    iteratedDeriv j (leftFullCoefficient N) s =
      iteratedDeriv j (leftOnsiteFormFactor N) s +
      2*iteratedDeriv j (leftFormFactor N) s := by
  have hO := leftOnsiteFormFactor_analyticAt N hN hs
  have hD : AnalyticAt ℂ (fun t => (2:ℂ)*leftFormFactor N t) s :=
    (analyticAt_const (v := (2:ℂ))).mul (leftFormFactor_analyticAt N hN hs)
  unfold leftFullCoefficient
  rw [iteratedDeriv_fun_add hO.contDiffAt hD.contDiffAt,
    iteratedDeriv_const_mul_field]

theorem leftFullOdd_derivative_summable (j : ℕ) {s : ℂ}
    (hs : (sourceS s).re < -2) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (leftFullCoefficient (2*n+1)) s‖) := by
  have hO := leftOnsiteOdd_derivative_summable j hs
  have hD := (leftOdd_derivative_summable j hs).mul_left 2
  apply (hO.add hD).of_norm_bounded
  intro n
  rw [norm_norm,leftFullCoefficient_iteratedDeriv _ (by omega) j hs]
  simpa only [norm_mul,Complex.norm_ofNat] using norm_add_le
    (iteratedDeriv j (leftOnsiteFormFactor (2*n+1)) s)
    (2*iteratedDeriv j (leftFormFactor (2*n+1)) s)

theorem leftFullOddSeries_eq_onsite_add_offsite {s : ℂ}
    (hs : (sourceS s).re < -2) :
    leftFullOddSeries s = leftOnsiteOddSeries s + 2*leftOddSeries s := by
  have hO : Summable (fun n : ℕ => leftOnsiteFormFactor (2*n+1) s) :=
    (leftOnsiteOdd_derivative_summable 0 hs).of_norm
  have hD : Summable (fun n : ℕ => leftFormFactor (2*n+1) s) :=
    (leftOdd_derivative_summable 0 hs).of_norm
  simp only [leftFullOddSeries,leftFullCoefficient,leftOnsiteOddSeries,leftOddSeries]
  rw [hO.tsum_add (hD.mul_left 2),tsum_mul_left]

theorem leftFullOddSeries_analyticAt {s : ℂ} (hs : (sourceS s).re < -2) :
    AnalyticAt ℂ leftFullOddSeries s := by
  have he : leftFullOddSeries =ᶠ[𝓝 s]
      (fun t => leftOnsiteOddSeries t + 2*leftOddSeries t) := by
    filter_upwards [leftTraceDomain_isOpen.mem_nhds hs] with t ht
    exact leftFullOddSeries_eq_onsite_add_offsite ht
  exact ((leftOnsiteOddSeries_analyticAt hs).add
    ((analyticAt_const (v := (2:ℂ))).mul (leftOddSeries_analyticAt hs))).congr he.symm

theorem leftFullOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    leftFullOddSeries s = fixedOddFullSeries r s := by
  apply tsum_congr
  intro n
  exact leftFullCoefficient_eq_fixed_radius _ (by omega) hr hr1 hm

/-- The two genuine source constructions agree on their overlap by a common
admissible radius, before the infinite sum is identified. -/
theorem leftFullCoefficient_eq_upper (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hr : (sourceS s).re < -2) (hu : 0 < (sourceS s).im) :
    leftFullCoefficient N s = upperFullCoefficient N s := by
  rw [leftFullCoefficient,upperFullCoefficient,
    leftOnsiteFormFactor_eq_upper N hN hr hu,leftFormFactor_eq_upper N hN hr hu]

theorem leftFullOddSeries_eq_upper {s : ℂ}
    (hr : (sourceS s).re < -2) (hu : 0 < (sourceS s).im) :
    leftFullOddSeries s = upperFullOddSeries s := by
  apply tsum_congr
  intro n
  exact leftFullCoefficient_eq_upper _ (by omega) hr hu

end
end IsingBulk.HT.Final
