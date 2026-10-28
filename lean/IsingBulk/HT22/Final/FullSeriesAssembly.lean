import IsingBulk.HT22.Final.SignedObstruction
import IsingBulk.HT22.FullTail.EpsilonLimit

/-! The infinite tail is discharged by the new complete physical proof.
Only the still separate finite lower / first coefficient inputs are exposed
by this integration lemma; it is not a claimed completed endpoint. -/
namespace IsingBulk.HT22.Final
noncomputable section
open IsingBulk.HT22.Physical IsingBulk.HT22.Arithmetic IsingBulk.PrimeFamily
open IsingBulk.Preferred22 IsingBulk.Branch Filter
open scoped Topology BigOperators

theorem full_signed_series_limit (d : PreferredBranchData)
    {p : ℕ} (hp5 : 5≤p) (hp : Odd p) (negative : Bool) {j : ℕ}
    (hj : j≤IsingBulk.HT.First.derivativeOrder p) {L : ℂ}
    (hlow : ∀ n : ℕ,2*n+1<p →
      Tendsto (fun ε : ℝ => ε • iteratedDeriv j (signedCoefficient negative (2*n+1))
        (radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 0))
    (hfirst : Tendsto (fun ε : ℝ => ε • iteratedDeriv j (signedCoefficient negative p)
      (radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv j (signedOddSeries negative)
      (radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 L) := by
  have hq : 2*(p/2)+1=p := by obtain ⟨q,hq⟩ := hp;omega
  have hsum := tendsto_finsetSum (Finset.range (p/2)) (fun n hn =>
    hlow n (by have := Finset.mem_range.mp hn;omega))
  have hlow' : Tendsto (fun ε : ℝ => ε •
      (∑ n∈Finset.range (p/2),iteratedDeriv j (signedCoefficient negative (2*n+1))
        (radialParameter d.alpha ε))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Finset.smul_sum,Finset.sum_const_zero] using hsum
  apply signed_series_limit_of_three_limits negative (p/2) j d.alpha hlow'
  · simpa only [hq] using hfirst
  · exact FullTail.actual_tail_epsilon_zero_split d hp5 hp hj negative

theorem prime_obstruction_of_finite_limits {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {L : ℂ} (hL : L≠0)
    (hlow : ∀ n : ℕ,2*n+1<p →
      Tendsto (fun ε : ℝ => ε • iteratedDeriv (IsingBulk.HT.First.derivativeOrder p)
        (signedCoefficient (negativeSide (angle p a)) (2*n+1))
        (radialParameter (primeBranchData hp hp5 ha).alpha ε)) (𝓝[>] 0) (𝓝 0))
    (hfirst : Tendsto (fun ε : ℝ => ε • iteratedDeriv (IsingBulk.HT.First.derivativeOrder p)
      (signedCoefficient (negativeSide (angle p a)) p)
      (radialParameter (primeBranchData hp hp5 ha).alpha ε)) (𝓝[>] 0) (𝓝 L)) :
    ¬IsingBulk.Final.HasExteriorExtension oddSeries (angleRoot p a) := by
  have hseries := full_signed_series_limit (primeBranchData hp hp5 ha) hp5
    (hp.odd_of_ne_two (by omega)) (negativeSide (angle p a)) le_rfl hlow hfirst
  apply no_extension_original_of_effective_signed
  apply IsingBulk.HT.Final.no_extension_of_nonzero_epsilon_radial_limit
    (Complex.norm_exp_ofReal_mul_I _) hL (IsingBulk.HT.First.derivativeOrder p)
  simpa only [radialParameter,primeBranchData,positiveTraceBranchData,
    Complex.ofReal_add,Complex.ofReal_one] using hseries

end
end IsingBulk.HT22.Final
