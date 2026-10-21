import IsingBulk.HT.Final.UpperFullSeries
import IsingBulk.HT.Tail.OddIndexing
import IsingBulk.First.MeanParameterDisk

/-! Exact differentiated full-site source identities, before any boundary limit. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail IsingBulk.Branch Filter Set
open scoped Topology BigOperators

theorem upperFullCoefficient_iteratedDeriv_fixed_radius (N : ℕ) (hN : 0 < N)
    (j : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) :
    iteratedDeriv j (upperFullCoefficient N) s =
      iteratedDeriv j (standardFormFactor N r) s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  exact upperFullCoefficient_eq_fixed_radius N hN hr hr1 ht.2

theorem upperFullOddSeries_iteratedDeriv (j : ℕ) {s : ℂ}
    (hs : 0 < (sourceS s).im) :
    iteratedDeriv j upperFullOddSeries s =
      ∑' n : ℕ, iteratedDeriv j (upperFullCoefficient (2*n+1)) s := by
  have he : upperFullOddSeries =ᶠ[𝓝 s]
      (fun t => upperOnsiteOddSeries t+2*upperOddSeries t) := by
    filter_upwards [upperTraceDomain_isOpen.mem_nhds hs] with t ht
    exact upperFullOddSeries_eq_onsite_add_offsite ht
  have hO := upperOnsiteOddSeries_analyticAt hs
  have hD : AnalyticAt ℂ (fun t => (2:ℂ)*upperOddSeries t) s :=
    (analyticAt_const (v := (2:ℂ))).mul (upperOddSeries_analyticAt hs)
  rw [Filter.EventuallyEq.iteratedDeriv_eq j he,
    iteratedDeriv_fun_add hO.contDiffAt hD.contDiffAt,iteratedDeriv_const_mul_field,
    upperOnsiteOddSeries_iteratedDeriv j hs,upperOddSeries_iteratedDeriv j hs]
  have hOs := (upperOnsiteOdd_derivative_summable j hs).of_norm
  have hDs := (upperOdd_derivative_summable j hs).of_norm
  rw [← tsum_mul_left,← hOs.tsum_add (hDs.mul_left 2)]
  apply tsum_congr
  intro n
  exact (upperFullCoefficient_iteratedDeriv _ (by omega) j hs).symm

/-- Low orders, the first particle number, and every higher odd particle
number partition the convergent differentiated full-site series exactly. -/
theorem upperFullOddSeries_radial_split (q j : ℕ) {theta eps : ℝ}
    (htheta : 0 < Real.sin theta) (heps : 0 < eps) :
    iteratedDeriv j upperFullOddSeries (radialParameter theta eps) =
      (∑ n ∈ Finset.range q,
        iteratedDeriv j (upperFullCoefficient (2*n+1)) (radialParameter theta eps)) +
      iteratedDeriv j (upperFullCoefficient (2*q+1)) (radialParameter theta eps) +
      ∑' n : ℕ, iteratedDeriv j (upperFullCoefficient (oddTailParticle (2*q+1) n))
        (radialParameter theta eps) := by
  have hs := IsingBulk.Final.sourceRadialTrace_pos htheta heps
  rw [upperFullOddSeries_iteratedDeriv j hs]
  have hsum := (upperFullOdd_derivative_summable j hs).of_norm.sum_add_tsum_nat_add (q+1)
  rw [Finset.sum_range_succ] at hsum
  have hindex (n : ℕ) : 2*(n+(q+1))+1 = oddTailParticle (2*q+1) n := by
    dsimp only [oddTailParticle]
    omega
  simpa only [hindex] using hsum.symm

/-- A single source-radius neighborhood works for every finite particle
number and derivative order; the equality differentiates at fixed radius. -/
theorem radial_upper_full_derivatives (N : ℕ) (hN : 0 < N)
    {theta : ℝ} (htheta : 0 < Real.sin theta) :
    ∃ d : ℝ, 0 < d ∧ ∀ eps : ℝ, 0 < eps → eps < d → ∀ j : ℕ,
      iteratedDeriv j (upperFullCoefficient N) (radialParameter theta eps) =
        (deriv^[j] (standardFormFactor N (sourceRadialPair theta eps).1))
          (sourceRadialPair theta eps).2 := by
  obtain ⟨d,hd,_,hMargin⟩ := radial_disk_source_trace_margin htheta
  refine ⟨d,hd,?_⟩
  intro eps he heD j
  have hr : 0 < (sourceRadialPair theta eps).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair theta eps).1 < 1 := by
    change Real.exp (-(Real.sin theta/4)*eps) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos htheta he]
  have hwidth : 0 < Real.sin theta / 16 * eps :=
    mul_pos (div_pos htheta (by norm_num)) he
  have hm := (hMargin eps he heD (radialParameter theta eps)
    (by simpa using hwidth)).2
  simpa only [iteratedDeriv_eq_iterate,sourceRadialPair] using
    upperFullCoefficient_iteratedDeriv_fixed_radius N hN j hr hr1 hm

end
end IsingBulk.HT.Final
