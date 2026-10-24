import IsingBulk.Anisotropic.NegativeNormalForm.ComplexDensityBeta
import IsingBulk.Anisotropic.NegativeNormalForm.FullDensityEnvelope
import IsingBulk.Anisotropic.NegativeCycles.FreeHomotopy

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped BigOperators

theorem density_energy_to_exponential (u x s K : ℝ) (hu : 0≤u) (hx : 0≤x)
    (hs : 0≤s) (hK : 0≤K) (hux : u≤s*x) :
    K*(Real.sqrt u+u)*Real.exp (K*(Real.sqrt u+u))≤
      Real.exp ((2*K*(s+1))*(Real.sqrt x+x))-1 := by
  have hsqrt : Real.sqrt s≤s+1 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_nonneg s]
  have hb : Real.sqrt u+u≤(s+1)*(Real.sqrt x+x) := by
    have hroot := Real.sqrt_le_sqrt hux
    rw [Real.sqrt_mul hs] at hroot
    have hm := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg x)
    have hxs : s*x≤(s+1)*x := by nlinarith
    nlinarith
  apply (mul_exp_le_exp_two_sub_one _ (by positivity)).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hb (show 0≤2*K by positivity)
  nlinarith

theorem beta_coordinate_energy_control (N tau h Q : ℝ) (hN : 0<N) (ht : 0<tau)
    (hh : (1:ℝ)/2≤h) (hQ : 0≤Q) (hscale : 2*N^2*tau≤Real.pi^2) :
    N*Q≤(2*Real.pi^2)*(h/(2*N)*Q/tau) := by
  have hden : 0<2*N*tau := by positivity
  have hpi : 0≤Real.pi^2 := sq_nonneg _
  have he : h/(2*N)*Q/tau=h*Q/(2*N*tau) := by ring
  rw [he,←mul_div_assoc]
  apply (le_div_iff₀ hden).2
  have h1 := mul_le_mul_of_nonneg_right hscale hQ
  have h2 := mul_le_mul_of_nonneg_left hh (show 0≤2*Real.pi^2*Q by positivity)
  nlinarith

theorem realFreeChart_absoluteEnergy {n : ℕ} (q : Fin n→ℝ) :
    absoluteEnergy (freeChartCLM n (complexify n q))=constrainedSquaredRadius q := by
  rw [freeChartCLM_eq_shapeExtend,shapeExtend_complexify,absoluteEnergy_real]
  rfl

theorem cutoff_freeChart_lt {n : ℕ} (b : ContDiffBump (0:ℝ)) (delta : ℝ)
    (hdelta : 0<delta) (hb : b.rOut<delta^2) (q : Fin n→ℝ)
    (hq : shapeSpatialCutoff b q≠0) : ‖freeChartCLM n (complexify n q)‖<delta := by
  have hQ : constrainedSquaredRadius q<b.rOut := by
    by_contra h
    exact hq (shapeSpatialCutoff_zero b (le_of_not_gt h))
  have hn := norm_sq_le_absoluteEnergy (freeChartCLM n (complexify n q))
  rw [realFreeChart_absoluteEnergy] at hn
  nlinarith [norm_nonneg (freeChartCLM n (complexify n q))]

end
end IsingBulk.Anisotropic.NegativeNormalForm
