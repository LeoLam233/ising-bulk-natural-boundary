import IsingBulk.First.RadialDiskAdmissibility
import IsingBulk.HT22.Physical.SignedConvergence
import IsingBulk.Analysis.BranchRadial

/-! Exact splitting of the actual entire signed odd series at any odd order.
This uses compact normal convergence only, not a boundary tail endpoint. -/
namespace IsingBulk.HT22.Final
noncomputable section
open IsingBulk.HT22.Physical IsingBulk.Branch Filter
open scoped Topology BigOperators

theorem signedOddSeries_derivative_split (negative : Bool) (q j : ℕ)
    {t : ℂ} (ht : 1<‖t‖) :
    iteratedDeriv j (signedOddSeries negative) t =
      (∑ n ∈ Finset.range q,iteratedDeriv j (signedCoefficient negative (2*n+1)) t) +
      iteratedDeriv j (signedCoefficient negative (2*q+1)) t +
      ∑' n : ℕ,iteratedDeriv j (signedCoefficient negative (2*q+3+2*n)) t := by
  rw [signedOddSeries_iteratedDeriv negative j ht]
  have hsum := (signedOdd_derivative_norm_summable negative j ht).of_norm.sum_add_tsum_nat_add (q+1)
  rw [Finset.sum_range_succ] at hsum
  have hindex (n : ℕ) : 2*(n+(q+1))+1=2*q+3+2*n := by omega
  simpa only [hindex] using hsum.symm

theorem signedOddSeries_conjugate (negative : Bool) {t : ℂ} (ht : 1<‖t‖) :
    signedOddSeries negative (star t)=star (signedOddSeries negative t) := by
  unfold signedOddSeries
  simp_rw [signedCoefficient_conj negative _ ht]
  exact tsum_star.symm

/-- Finite lower orders, the first coefficient and the infinite upper tail
are the three genuine analytic obligations for noncancellation. This lemma
is not claimed as their proof. -/
theorem signed_series_limit_of_three_limits (negative : Bool) (q j : ℕ) (α : ℝ) {L : ℂ}
    (hlow : Tendsto (fun ε : ℝ => ε •
      (∑ n ∈ Finset.range q,iteratedDeriv j (signedCoefficient negative (2*n+1))
        (radialParameter α ε))) (𝓝[>] 0) (𝓝 0))
    (hfirst : Tendsto (fun ε : ℝ => ε •
      iteratedDeriv j (signedCoefficient negative (2*q+1)) (radialParameter α ε))
      (𝓝[>] 0) (𝓝 L))
    (htail : Tendsto (fun ε : ℝ => ε •
      (∑' n : ℕ,iteratedDeriv j (signedCoefficient negative (2*q+3+2*n))
        (radialParameter α ε))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv j (signedOddSeries negative)
      (radialParameter α ε)) (𝓝[>] 0) (𝓝 L) := by
  have h := (hlow.add hfirst).add htail
  simp only [zero_add,add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : 0<ε := hε
  have ht : 1<‖radialParameter α ε‖ := by
    rw [IsingBulk.First.radialParameter_norm he.le]
    linarith
  rw [signedOddSeries_derivative_split negative q j ht,smul_add,smul_add]

end
end IsingBulk.HT22.Final
