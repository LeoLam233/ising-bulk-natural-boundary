import IsingBulk.HT.Final.PhysicalNormalization
import IsingBulk.HT.Final.UpperOnsiteSeries
import IsingBulk.HT.Tail.UpperOddSeries

/-! The actual full-site odd series on the upper-trace chart. Both onsite
and offsite normal convergence are constructed before summing. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail Set Filter Metric
open scoped Topology BigOperators

def upperFullCoefficient (N : ℕ) (s : ℂ) : ℂ :=
  upperOnsiteFormFactor N s + 2*upperFormFactor N s

def upperFullOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, upperFullCoefficient (2*n+1) s

theorem upperFullCoefficient_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperFullCoefficient N s = standardFormFactor N r s := by
  rw [upperFullCoefficient, upperOnsiteFormFactor_eq_fixed_radius N hN hr hr1 hm,
    upperFormFactor_eq_fixed_radius N hN hr hr1 hm]
  exact (standardFormFactor_eq_onsite_add_double N hN r s (globalRoot s)
    (globalRoot_admissible hr hr1 hm)).symm

theorem upperFullCoefficient_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 0 < (sourceS s).im) : AnalyticAt ℂ (upperFullCoefficient N) s :=
  (upperOnsiteFormFactor_analyticAt N hN hs).add
    ((analyticAt_const (v := (2:ℂ))).mul (upperFormFactor_analyticAt N hN hs))

theorem upperFullCoefficient_iteratedDeriv (N : ℕ) (hN : 0 < N) (j : ℕ) {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    iteratedDeriv j (upperFullCoefficient N) s =
      iteratedDeriv j (upperOnsiteFormFactor N) s +
      2*iteratedDeriv j (upperFormFactor N) s := by
  have hO := upperOnsiteFormFactor_analyticAt N hN hs
  have hD : AnalyticAt ℂ (fun t => (2:ℂ)*upperFormFactor N t) s :=
    (analyticAt_const (v := (2:ℂ))).mul (upperFormFactor_analyticAt N hN hs)
  unfold upperFullCoefficient
  rw [iteratedDeriv_fun_add hO.contDiffAt hD.contDiffAt,
    iteratedDeriv_const_mul_field]

theorem upperFullOdd_derivative_summable (j : ℕ) {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFullCoefficient (2*n+1)) s‖) := by
  have hO := upperOnsiteOdd_derivative_summable j hs
  have hD := (upperOdd_derivative_summable j hs).mul_left 2
  apply (hO.add hD).of_norm_bounded
  intro n
  rw [norm_norm,upperFullCoefficient_iteratedDeriv _ (by omega) j hs]
  simpa only [norm_mul,Complex.norm_ofNat] using norm_add_le
    (iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) s)
    (2*iteratedDeriv j (upperFormFactor (2*n+1)) s)

theorem upperFullOddSeries_eq_onsite_add_offsite {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    upperFullOddSeries s = upperOnsiteOddSeries s + 2*upperOddSeries s := by
  have hO : Summable (fun n : ℕ => upperOnsiteFormFactor (2*n+1) s) :=
    (upperOnsiteOdd_derivative_summable 0 hs).of_norm
  have hD : Summable (fun n : ℕ => upperFormFactor (2*n+1) s) :=
    (upperOdd_derivative_summable 0 hs).of_norm
  simp only [upperFullOddSeries,upperFullCoefficient,upperOnsiteOddSeries,upperOddSeries]
  rw [hO.tsum_add (hD.mul_left 2),tsum_mul_left]

theorem upperFullOddSeries_analyticAt {s : ℂ} (hs : 0 < (sourceS s).im) :
    AnalyticAt ℂ upperFullOddSeries s := by
  have he : upperFullOddSeries =ᶠ[𝓝 s]
      (fun t => upperOnsiteOddSeries t + 2*upperOddSeries t) := by
    filter_upwards [upperTraceDomain_isOpen.mem_nhds hs] with t ht
    exact upperFullOddSeries_eq_onsite_add_offsite ht
  exact ((upperOnsiteOddSeries_analyticAt hs).add
    ((analyticAt_const (v := (2:ℂ))).mul (upperOddSeries_analyticAt hs))).congr he.symm

theorem upperFullOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperFullOddSeries s = fixedOddFullSeries r s := by
  apply tsum_congr
  intro n
  exact upperFullCoefficient_eq_fixed_radius _ (by omega) hr hr1 hm

end
end IsingBulk.HT.Final
