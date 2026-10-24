import IsingBulk.Anisotropic.NegativeNormalForm.RelativeDensityAlgebra

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

/-- Convert the exact complex logarithm envelope into Gaussian radial growth,
without losing the leading square-root error at beta concentration scale. -/
theorem energy_envelope_absorb_sqrt (K : ℝ) (hK : 0<K) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 0≤x →
      K*(Real.sqrt x+x)*Real.exp (K*(Real.sqrt x+x))≤
        C*(Real.sqrt x+x)*Real.exp (C*x) := by
  let C := K*Real.exp (K^2/4)+K+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro x hx
  have hs := Real.sq_sqrt hx
  have harg : K*(Real.sqrt x+x)≤K^2/4+(K+1)*x := by nlinarith [sq_nonneg (Real.sqrt x-K/2)]
  have he := Real.exp_le_exp.mpr harg
  rw [Real.exp_add] at he
  have hKC : K+1≤C := by
    have hh : 0≤K*Real.exp (K^2/4) := by positivity
    dsimp [C]
    linarith
  have hcoeff : K*Real.exp (K^2/4)≤C := by dsimp [C]; linarith
  have hExpC : Real.exp ((K+1)*x)≤Real.exp (C*x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKC hx)
  calc
    _ ≤ K*(Real.sqrt x+x)*(Real.exp (K^2/4)*Real.exp ((K+1)*x)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (K*Real.exp (K^2/4))*(Real.sqrt x+x)*Real.exp ((K+1)*x) := by ring
    _ ≤ C*(Real.sqrt x+x)*Real.exp (C*x) := by gcongr

end
end IsingBulk.Anisotropic.NegativeNormalForm
