import IsingBulk.First.FirstTheorem
import IsingBulk.Final.LocalExtension

/-! Actual source attachment of the local obstruction to the previously
verified FIRST endpoint. This concerns the first carrier, not the full bulk sum. -/
namespace IsingBulk.Final
noncomputable section
open Filter IsingBulk.First IsingBulk.Branch
open scoped Topology

theorem selected_first_carrier_no_extension {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    ¬ HasExteriorExtension (upperFormFactor (2*p)) (PrimeFamily.selectedPoint p a b) := by
  obtain ⟨hL,hTop,_⟩ := first_upper_asymptotic hp hp11 ha hb hab
  have hn : 2*p-1+1=2*p := by have := hp.pos; omega
  simp only [hn] at hL hTop
  let A := selectedOrderedChart ha hb
  let k := (2*p)^2/2-1
  let L := localLeadingCoefficient A (2*p-1) k
  have hz : ‖PrimeFamily.selectedPoint p a b‖ = 1 := by
    unfold PrimeFamily.selectedPoint
    exact Complex.norm_exp_ofReal_mul_I _
  apply no_extension_of_nonzero_radial_limit hz
    (show 2*L ≠ 0 from mul_ne_zero (by norm_num) hL) k
  have hlim := sqrt_limit_of_isLittleO hTop
  convert hlim using 1
  funext e
  congr 2
  simp only [radialParameter,PrimeFamily.selectedPoint,selectedOrderedChart,
    Complex.ofReal_add,Complex.ofReal_one]

end
end IsingBulk.Final
