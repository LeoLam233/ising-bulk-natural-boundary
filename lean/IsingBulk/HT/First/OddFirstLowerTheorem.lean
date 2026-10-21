import IsingBulk.HT.First.OddFirstUpperLowerLimit
import IsingBulk.First.FirstTheorem
import IsingBulk.First.OnsiteGlobalBound
import IsingBulk.First.NormalizationDerivatives

/-! Actual HT lower-jet comparison, including the critical logarithmic order.
The conclusion is the precise scale needed to isolate the first singular jet;
no uniform O(1) claim is made at j=k−1. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.Branch IsingBulk.First
open scoped Topology

/-- Every actual lower offsite jet is negligible on the ε⁻¹ scale. -/
theorem first_fixed_odd_source_lower_littleO {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) (j : ℕ) (hj : j < derivativeOrder p) :
    let A := selectedOrderedChart ha hb
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[j] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2)
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  have hN : p-1+1=p := by have := hp.pos; omega
  have hTop := first_upper_odd_lower_littleO hp hp11 ha hb hab j hj
  simp only [hN] at hTop
  obtain ⟨d,hd,hRep⟩ := radial_upper_double_derivatives p hp.pos
    (selectedOrderedChart ha hb).sin_theta_pos
  apply hTop.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with epsilon he heD
  rw [hRep epsilon he heD]

/-- The same lower-jet conclusion for the literal full-site C_p=f_p+2T_p. -/
theorem first_standard_odd_source_lower_littleO {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) (j : ℕ) (hj : j < derivativeOrder p) :
    let A := selectedOrderedChart ha hb
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[j] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2)
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  let A := selectedOrderedChart ha hb
  have hTop := first_fixed_odd_source_lower_littleO hp hp11 ha hb hab j hj
  have hlevel := PrimeFamily.cosineAverage_bounds ha hb
  have hS : sourceS (exp ((A.theta:ℂ)*I)) = ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,A,Complex.ofReal_mul,
      Complex.ofReal_ofNat] using PrimeFamily.selectedPoint_relation ha hb
  obtain ⟨e,he,hO⟩ := onsite_global_radial_bound hp.pos
    (2*PrimeFamily.cosineAverage p a b) (by constructor <;> linarith)
    A.theta A.sin_theta_pos hS
  obtain ⟨C,_hC,hC⟩ := hO j
  have hOn := bounded_radial_term_epsilon_isLittleO he hC
  obtain ⟨d,hd,_,hMargin⟩ := radial_disk_source_trace_margin A.sin_theta_pos
  apply (hOn.add (hTop.add hTop)).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with epsilon heps heD
  have hr : 0 < (sourceRadialPair A.theta epsilon).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair A.theta epsilon).1 < 1 := by
    change Real.exp (-(Real.sin A.theta/4)*epsilon) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos A.sin_theta_pos heps]
  have hm := (hMargin epsilon heps heD (radialParameter A.theta epsilon)
    (by simpa using mul_pos (div_pos A.sin_theta_pos (by norm_num) : 0 < Real.sin A.theta/16) heps)).2
  have hEq : (deriv^[j] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
      (sourceRadialPair A.theta epsilon).2 =
      (deriv^[j] (onsiteFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2+
      2*(deriv^[j] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2 := by
    simpa only [iteratedDeriv_eq_iterate,sourceRadialPair] using
      standardFormFactor_iteratedDeriv_eq p hp.pos j hr hr1 hm
  rw [hEq]
  ring


end
end IsingBulk.HT.First
