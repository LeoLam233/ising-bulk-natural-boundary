import IsingBulk.First.MeanPhase
import IsingBulk.First.MeanPole
import IsingBulk.Algebra.SelectedPoint

/-! Instantiation of the regular mean-chart data by the frozen prime family. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.PrimeFamily

/-- Constructed from the literal selected prime-family angles. No local
analytic estimate or desired residue identity is supplied as data. -/
def selectedOrderedChart {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) : OrderedChartData where
  alpha := angle p a
  beta := angle p b
  theta := Real.arccos (cosineAverage p a b)
  alpha_pos := ha.1
  alpha_lt := ha.2
  beta_pos := hb.1
  beta_lt := hb.2
  theta_pos := Real.arccos_pos.mpr (cosineAverage_bounds ha hb).2
  theta_lt := Real.arccos_lt_pi_div_two.mpr (cosineAverage_bounds ha hb).1
  angle_relation := by
    have hc := cosineAverage_bounds ha hb
    rw [Real.cos_arccos (by linarith) hc.2.le]
    unfold cosineAverage
    ring

/-- The selected lower center has exactly the particle-order root identity
needed for the physical Y pole, proved from the frozen primitive-root result. -/
theorem selected_lower_center_root {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : Admissible p a) :
    Complex.exp (-((2*p:ℕ):ℂ)*(angle p a:ℂ)*Complex.I) = 1 := by
  have hpw : angleRoot p a ^ p = 1 := (angleRoot_primitive hp ha).pow_eq_one
  have hN : angleRoot p a ^ (2*p) = 1 := by rw [Nat.mul_comm 2 p, pow_mul, hpw, one_pow]
  have he : -((2*p:ℕ):ℂ)*(angle p a:ℂ)*Complex.I =
      -((2*p:ℕ):ℂ)*((angle p a:ℂ)*Complex.I) := by ring
  rw [he, neg_mul, Complex.exp_neg, Complex.exp_nat_mul]
  change (angleRoot p a ^ (2*p))⁻¹ = 1
  rw [hN, inv_one]

theorem selected_meanProductY_at_pole {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : Admissible p a) (rho : ℝ) :
    meanProductY (2*p) rho (angle p a) (physicalMeanPole (2*p) rho) = 1 :=
  meanProductY_at_physicalMeanPole (2*p) rho (angle p a) (selected_lower_center_root hp ha)

theorem selected_mean_pole_derivative {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : Admissible p a) (rho : ℝ) :
    HasDerivAt (fun v => 1-meanProductY (2*p) rho (angle p a) v) (-Complex.I)
      (physicalMeanPole (2*p) rho) :=
  one_sub_meanProductY_pole_derivative (2*p) rho (angle p a) (selected_lower_center_root hp ha)

end
end IsingBulk.First
