import IsingBulk.HT.First.OddFirstUpperAsymptotic
import IsingBulk.First.FirstTheorem
import IsingBulk.First.OnsiteGlobalBound
import IsingBulk.First.NormalizationDerivatives

/-! Positive-prime-family actual HT first singularity. The coefficient here is
identified with the literal constrained shape period and is nonzero. Its
closed Hermite/factorial evaluation, the negative-cosine family, and the sharp
lower-derivative logarithm remain separate obligations. This file does not
assert the complete manuscript FIRST theorem or natural-boundary endpoint. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.Branch IsingBulk.First
open scoped Topology

/-- Actual fixed-radius T_p has the two equal local chart contributions. -/
theorem first_fixed_odd_source_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := selectedOrderedChart ha hb
    let L := oddLocalLeadingCoefficient A p
    L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2-(epsilon:ℂ)⁻¹*(2*L))
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  have hN : p-1+1=p := by have := hp.pos; omega
  obtain ⟨hL,hTop⟩ := first_upper_odd_asymptotic hp hp11 ha hb hab
  simp only [hN] at hL hTop
  obtain ⟨d,hd,hRep⟩ := radial_upper_double_derivatives p hp.pos
    (selectedOrderedChart ha hb).sin_theta_pos
  refine ⟨hL,?_⟩
  apply hTop.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with epsilon he heD
  rw [hRep epsilon he heD, oddLocalLeadingCoefficient]

/-- Exact factor four for the actual full-site C_p=f_p+2T_p. The onsite
estimate and fixed-radius derivative normalization are imported proved
parity-free results, not supplied as asymptotic assumptions. -/
theorem first_standard_odd_source_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := selectedOrderedChart ha hb
    let L := oddLocalLeadingCoefficient A p
    4*L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2-(epsilon:ℂ)⁻¹*(4*L))
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  let A := selectedOrderedChart ha hb
  let k := derivativeOrder p
  obtain ⟨hL,hTop⟩ := first_fixed_odd_source_asymptotic hp hp11 ha hb hab
  have hlevel := PrimeFamily.cosineAverage_bounds ha hb
  have hS : sourceS (exp ((A.theta:ℂ)*I)) = ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,A,Complex.ofReal_mul,
      Complex.ofReal_ofNat] using PrimeFamily.selectedPoint_relation ha hb
  obtain ⟨e,he,hO⟩ := onsite_global_radial_bound hp.pos
    (2*PrimeFamily.cosineAverage p a b) (by constructor <;> linarith)
    A.theta A.sin_theta_pos hS
  obtain ⟨C,_hC,hC⟩ := hO k
  have hOn := bounded_radial_term_epsilon_isLittleO he hC
  obtain ⟨d,hd,_,hMargin⟩ := radial_disk_source_trace_margin A.sin_theta_pos
  refine ⟨mul_ne_zero (by norm_num) hL,?_⟩
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
  have hEq : (deriv^[k] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
      (sourceRadialPair A.theta epsilon).2 =
      (deriv^[k] (onsiteFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2+
      2*(deriv^[k] (doubleFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2 := by
    simpa only [iteratedDeriv_eq_iterate,sourceRadialPair] using
      standardFormFactor_iteratedDeriv_eq p hp.pos k hr hr1 hm
  rw [hEq]
  ring

end
end IsingBulk.HT.First
