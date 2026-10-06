import IsingBulk.First.LowerOrderTransfer
import IsingBulk.Final.RadialNoncancellation

/-! The finite lower-order sum uses exactly the existing E3 interface and
its internally proved full-site to offsite transfer. -/
namespace IsingBulk.Final
noncomputable section
open Filter IsingBulk.First IsingBulk.Branch
open scoped Topology BigOperators

theorem lower_even_sum_isLittleO {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b)) (j : ℕ) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun e => ∑ n ∈ Finset.range (p-1),
        iteratedDeriv j (upperFormFactor (2*(n+1)))
          (radialParameter (selectedOrderedChart ha hb).theta e))
      (fun e => (Real.sqrt e:ℂ)⁻¹) := by
  apply Asymptotics.IsLittleO.fun_sum
  intro n hn
  have hnp : 2*(n+1) < 2*p := by
    have hn' := Finset.mem_range.mp hn
    omega
  obtain ⟨d,C,hd,_,hbound⟩ := selected_lower_orders_radial_bounded hp hp11 ha hb hTW
    (2*(n+1)) (by omega) (even_two_mul _) hnp j
  apply IsingBulk.First.bounded_radial_term_isLittleO (show 0 < d/2 by positivity)
  intro e he hed
  simpa only [iteratedDeriv_eq_iterate] using hbound e he (by linarith)

end
end IsingBulk.Final
