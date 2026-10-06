import IsingBulk.First.MeanPhaseSecond
import IsingBulk.First.MeanSelectedData
import IsingBulk.Analysis.BranchTaylor

/-! Actual radial trace and regular phase, with the contour-radius coefficient
kept explicit. Radial evaluation derivatives here are not s derivatives. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

def complexRadialTrace (theta : ℝ) (epsilon : ℂ) : ℂ :=
  (1+epsilon)*Complex.exp ((theta:ℂ)*Complex.I) +
    ((1+epsilon)*Complex.exp ((theta:ℂ)*Complex.I))⁻¹

theorem complexRadialTrace_zero (theta : ℝ) :
    complexRadialTrace theta 0 = 2*(Real.cos theta:ℂ) := by
  simpa [complexRadialTrace] using IsingBulk.PrimeFamily.exp_angle_add_inv theta

theorem complexRadialTrace_hasDerivAt_zero (theta : ℝ) :
    HasDerivAt (complexRadialTrace theta) (2*Complex.I*(Real.sin theta:ℂ)) 0 := by
  let z := Complex.exp ((theta:ℂ)*Complex.I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hs : HasDerivAt (fun e : ℂ => (1+e)*z) z 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_add 1).mul_const z
  have hh := hs.add (hs.inv (by simpa using hz))
  have hcoef : z + -(z/((1+(0:ℂ))*z)^2) = 2*Complex.I*(Real.sin theta:ℂ) := by
    have hdiff : z-z⁻¹ = 2*Complex.I*(Real.sin theta:ℂ) := by
      have hm : z⁻¹ = Complex.exp (-(theta:ℂ)*Complex.I) := by
        dsimp [z]
        rw [← Complex.exp_neg]
        congr 1
        ring
      rw [hm]
      dsimp [z]
      rw [Complex.exp_mul_I, Complex.exp_mul_I]
      simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_sin]
      ring
    rw [← hdiff]
    field_simp
    ring
  convert! hh using 1
  simpa only [neg_div] using hcoef.symm

/-- Exactly W for radial s and logarithmic radius -c₀ epsilon. -/
def radialRegularW (a : OrderedChartData) (c₀ : ℝ) (epsilon u : ℂ) : ℂ :=
  complexRadialTrace a.theta epsilon -
    Complex.cosh (-(c₀:ℂ)*epsilon+(u-(a.alpha:ℂ))*Complex.I)

def radialRegularPhase (a : OrderedChartData) (c₀ : ℝ) (epsilon u : ℂ) : ℂ :=
  lowerArccos (radialRegularW a c₀ epsilon u)

theorem radialRegularW_zero (a : OrderedChartData) (c₀ : ℝ) :
    radialRegularW a c₀ 0 0 = (Real.cos a.beta:ℂ) := by
  have ha : (Real.cos a.alpha:ℂ)+(Real.cos a.beta:ℂ)=2*(Real.cos a.theta:ℂ) := by
    exact_mod_cast a.angle_relation
  simp only [radialRegularW, complexRadialTrace_zero, mul_zero, zero_sub,
    zero_add, Complex.cosh_mul_I, Complex.cos_neg, ← Complex.ofReal_cos]
  linear_combination -ha

theorem radialRegularPhase_zero (a : OrderedChartData) (c₀ : ℝ) :
    radialRegularPhase a c₀ 0 0 = (a.beta:ℂ) := by
  rw [radialRegularPhase, radialRegularW_zero]
  exact lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])

theorem radialRegularW_radial_derivative (a : OrderedChartData) (c₀ : ℝ) :
    HasDerivAt (fun e => radialRegularW a c₀ e 0)
      (Complex.I*(2*(Real.sin a.theta:ℂ)-(c₀:ℂ)*(Real.sin a.alpha:ℂ))) 0 := by
  have hinner : HasDerivAt (fun e : ℂ => -(c₀:ℂ)*e+(0-(a.alpha:ℂ))*Complex.I)
      (-(c₀:ℂ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_mul (-(c₀:ℂ))).add_const
      ((0-(a.alpha:ℂ))*Complex.I)
  have hcosh := hinner.ccosh
  have hh := (complexRadialTrace_hasDerivAt_zero a.theta).sub hcosh
  convert! hh using 1
  simp only [mul_zero, zero_sub, zero_add, Complex.sinh_mul_I, Complex.sin_neg,
    ← Complex.ofReal_sin]
  ring

theorem radialRegularPhase_radial_derivative (a : OrderedChartData) (c₀ : ℝ) :
    HasDerivAt (fun e => radialRegularPhase a c₀ e 0) (-Complex.I*(a.A₀ c₀:ℂ)) 0 := by
  have ho := lowerArccos_hasDerivAt_regular (Real.cos a.beta:ℂ)
    (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt)
  have hh := ho.comp_of_eq 0 (radialRegularW_radial_derivative a c₀)
    (radialRegularW_zero a c₀).symm
  change HasDerivAt (fun e => radialRegularPhase a c₀ e 0) _ 0 at hh
  convert! hh using 1
  rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])]
  simp only [OrderedChartData.A₀, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat, ← Complex.ofReal_sin]
  ring

end
end IsingBulk.First
