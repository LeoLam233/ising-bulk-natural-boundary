import IsingBulk.HT.Final.UpperFullSeries
import IsingBulk.HT.Final.RightOnsiteSeries
import IsingBulk.HT.Tail.RightOddSeries

/-! The actual full-site odd series on the right-trace chart. Both onsite
and offsite normal convergence are constructed before summing. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail Set Filter Metric
open scoped Topology BigOperators

def rightFullCoefficient (N : ℕ) (s : ℂ) : ℂ :=
  rightOnsiteFormFactor N s + 2*rightFormFactor N s

def rightFullOddSeries (s : ℂ) : ℂ := ∑' n : ℕ, rightFullCoefficient (2*n+1) s

theorem rightFullCoefficient_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    rightFullCoefficient N s = standardFormFactor N r s := by
  rw [rightFullCoefficient, rightOnsiteFormFactor_eq_fixed_radius N hN hr hr1 hm,
    rightFormFactor_eq_fixed_radius N hN hr hr1 hm]
  exact (standardFormFactor_eq_onsite_add_double N hN r s (rightRoot s)
    (rightRoot_admissible hr hr1 hm)).symm

theorem rightFullCoefficient_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 2 < (sourceS s).re) : AnalyticAt ℂ (rightFullCoefficient N) s :=
  (rightOnsiteFormFactor_analyticAt N hN hs).add
    ((analyticAt_const (v := (2:ℂ))).mul (rightFormFactor_analyticAt N hN hs))

theorem rightFullCoefficient_iteratedDeriv (N : ℕ) (hN : 0 < N) (j : ℕ) {s : ℂ}
    (hs : 2 < (sourceS s).re) :
    iteratedDeriv j (rightFullCoefficient N) s =
      iteratedDeriv j (rightOnsiteFormFactor N) s +
      2*iteratedDeriv j (rightFormFactor N) s := by
  have hO := rightOnsiteFormFactor_analyticAt N hN hs
  have hD : AnalyticAt ℂ (fun t => (2:ℂ)*rightFormFactor N t) s :=
    (analyticAt_const (v := (2:ℂ))).mul (rightFormFactor_analyticAt N hN hs)
  unfold rightFullCoefficient
  rw [iteratedDeriv_fun_add hO.contDiffAt hD.contDiffAt,
    iteratedDeriv_const_mul_field]

theorem rightFullOdd_derivative_summable (j : ℕ) {s : ℂ}
    (hs : 2 < (sourceS s).re) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (rightFullCoefficient (2*n+1)) s‖) := by
  have hO := rightOnsiteOdd_derivative_summable j hs
  have hD := (rightOdd_derivative_summable j hs).mul_left 2
  apply (hO.add hD).of_norm_bounded
  intro n
  rw [norm_norm,rightFullCoefficient_iteratedDeriv _ (by omega) j hs]
  simpa only [norm_mul,Complex.norm_ofNat] using norm_add_le
    (iteratedDeriv j (rightOnsiteFormFactor (2*n+1)) s)
    (2*iteratedDeriv j (rightFormFactor (2*n+1)) s)

theorem rightFullOddSeries_eq_onsite_add_offsite {s : ℂ}
    (hs : 2 < (sourceS s).re) :
    rightFullOddSeries s = rightOnsiteOddSeries s + 2*rightOddSeries s := by
  have hO : Summable (fun n : ℕ => rightOnsiteFormFactor (2*n+1) s) :=
    (rightOnsiteOdd_derivative_summable 0 hs).of_norm
  have hD : Summable (fun n : ℕ => rightFormFactor (2*n+1) s) :=
    (rightOdd_derivative_summable 0 hs).of_norm
  simp only [rightFullOddSeries,rightFullCoefficient,rightOnsiteOddSeries,rightOddSeries]
  rw [hO.tsum_add (hD.mul_left 2),tsum_mul_left]

theorem rightFullOddSeries_analyticAt {s : ℂ} (hs : 2 < (sourceS s).re) :
    AnalyticAt ℂ rightFullOddSeries s := by
  have he : rightFullOddSeries =ᶠ[𝓝 s]
      (fun t => rightOnsiteOddSeries t + 2*rightOddSeries t) := by
    filter_upwards [rightTraceDomain_isOpen.mem_nhds hs] with t ht
    exact rightFullOddSeries_eq_onsite_add_offsite ht
  exact ((rightOnsiteOddSeries_analyticAt hs).add
    ((analyticAt_const (v := (2:ℂ))).mul (rightOddSeries_analyticAt hs))).congr he.symm

theorem rightFullOddSeries_eq_fixed_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    rightFullOddSeries s = fixedOddFullSeries r s := by
  apply tsum_congr
  intro n
  exact rightFullCoefficient_eq_fixed_radius _ (by omega) hr hr1 hm

/-- The two genuine source constructions agree on their overlap by a common
admissible radius, before the infinite sum is identified. -/
theorem rightFullCoefficient_eq_upper (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hr : 2 < (sourceS s).re) (hu : 0 < (sourceS s).im) :
    rightFullCoefficient N s = upperFullCoefficient N s := by
  rw [rightFullCoefficient,upperFullCoefficient,
    rightOnsiteFormFactor_eq_upper N hN hr hu,rightFormFactor_eq_upper N hN hr hu]

theorem rightFullOddSeries_eq_upper {s : ℂ}
    (hr : 2 < (sourceS s).re) (hu : 0 < (sourceS s).im) :
    rightFullOddSeries s = upperFullOddSeries s := by
  apply tsum_congr
  intro n
  exact rightFullCoefficient_eq_upper _ (by omega) hr hu

end
end IsingBulk.HT.Final
