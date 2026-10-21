import IsingBulk.HT.First.ActualCoefficientPhase
import IsingBulk.HT.First.GaussianAngular

/-! Identification of the source-defined local coefficient with the literal
HT-1.0 Hermite-product formula. All angular and Gaussian normalization is
proved from the actual integral; the result has no analytic certificate or
additional asymptotic hypothesis. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.First Complex

 theorem odd_pi_pow_sub_one {p : ℕ} (hp : Odd p) :
    Real.pi^(p-1)=(Real.pi^((p-1)/2))^2 := by
  obtain ⟨q,hq⟩ := hp
  have he : p-1=((p-1)/2)*2 := by omega
  calc
    Real.pi^(p-1)=Real.pi^(((p-1)/2)*2) := congrArg (Real.pi^·) he
    _ = _ := pow_mul _ _ _

 theorem curvatureAmplitude_eq_closed {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    (theta H : ℝ) (hH : H ≠ 0) :
    curvatureAmplitude p theta H=closedAmplitudeMagnitude p theta H := by
  have hpR : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hAbs : 0 < |H| := abs_pos.mpr hH
  have hAngular := shapeAngularConstant_factorial_identity hp hp3
  unfold curvatureAmplitude closedAmplitudeMagnitude
  rw [odd_pi_pow_sub_one hp]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  calc
    _ = (shapeAngularConstant (p-1)*((derivativeOrder p-1).factorial:ℝ)*Real.sqrt p)*
        (Real.pi^((p-1)/2)*((p:ℝ)*Real.sin theta)^(derivativeOrder p-1)*
          |H|^derivativeOrder p) := by ring
    _ = _ := by rw [hAngular]; ring

namespace Regular

/-- Exact closed coefficient, simultaneously for positive and negative charts. -/
theorem oddLocalLeadingCoefficient_eq_closed (a : IsingBulk.First.RegularChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    oddLocalLeadingCoefficient a p=
      closedLeadingCoefficient p a.theta (curvatureNumerator a.alpha a.beta) := by
  rw [oddLocalLeadingCoefficient_eq_curvature a hp hp3,
    curvatureAmplitude_eq_closed hp hp3 a.theta (curvatureNumerator a.alpha a.beta)
      (curvatureNumerator_ne_zero a)]
  rfl

end Regular

/-- The ordered positive chart is the unchanged LT chart, via its proved
geometry-only map to the two-sign regular chart. -/
theorem oddLocalLeadingCoefficient_eq_closed (a : OrderedChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    oddLocalLeadingCoefficient a p=
      closedLeadingCoefficient p a.theta (curvatureNumerator a.alpha a.beta) := by
  exact Regular.oddLocalLeadingCoefficient_eq_closed a.toRegular hp hp3

end
end IsingBulk.HT.First
