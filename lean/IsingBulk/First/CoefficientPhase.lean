import IsingBulk.First.FirstCoefficient
import IsingBulk.First.ShapeArithmetic

/-! Exact source phase and parameter-derivative coefficient identities. -/
namespace IsingBulk.First
noncomputable section

/-- The explicit nonzero Ds is the source pole-derivative expression in S'. -/
theorem OrderedChartData.Ds_eq_sourceSPrime (a : OrderedChartData) (N : ℕ) :
    a.Ds N = -Complex.I * (N : ℂ) *
      IsingBulk.Jets.sourceSPrime (Complex.exp ((a.theta : ℂ)*Complex.I)) /
        (Real.sin a.beta : ℂ) := by
  have he : Complex.exp (-Complex.I*(a.theta : ℂ)) =
      (Complex.exp ((a.theta : ℂ)*Complex.I))⁻¹ := by
    rw [show -Complex.I*(a.theta : ℂ) = -((a.theta : ℂ)*Complex.I) by ring, Complex.exp_neg]
  have he' : Complex.exp (-(a.theta : ℂ)*Complex.I) =
      (Complex.exp ((a.theta : ℂ)*Complex.I))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  unfold OrderedChartData.Ds IsingBulk.Jets.sourceSPrime
  rw [Complex.ofReal_sin, Complex.sin, he, he']
  field_simp [Complex.exp_ne_zero, Complex.ofReal_ne_zero.mpr a.sin_beta_pos.ne']
  ring

end
end IsingBulk.First
