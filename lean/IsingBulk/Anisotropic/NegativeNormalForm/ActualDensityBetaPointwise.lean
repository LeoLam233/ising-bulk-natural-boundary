import IsingBulk.Anisotropic.NegativeNormalForm.DensityBetaEnergy
import IsingBulk.Anisotropic.NegativeNormalForm.ComplexPeriodLoss

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped BigOperators

theorem fullDensity_beta_pointwise {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (r Cp R delta K : ℝ)
    (P : UniformProjectedWitness B phi hphi (m+1) d r Cp)
    (J : UniformCorrectionWitness B phi hphi (m+1) d r Cp P R)
    (hdelta : 0<delta) (hK : 0≤K) (H : ℂ) (hH : (1:ℝ)/2≤H.re)
    (hfull : ∀u : Config m,‖freeChartCLM m u‖<delta →
      ‖normalizedFullDensity B rootB phi hphi d P.T (fun y=>P.V (J.W y)) u-1‖≤
        K*(Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
          (m+1:ℕ)*absoluteEnergy (freeChartCLM m u))*
        Real.exp (K*(Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
          (m+1:ℕ)*absoluteEnergy (freeChartCLM m u))))
    (b : ContDiffBump (0:ℝ)) (hb : b.rOut<delta^2) (q : Fin m→ℝ) :
    let c := H/((2*(m+1:ℕ):ℝ):ℂ)
    let L := 1+c.re*b.rOut/tau (m+1)
    ‖(shapeSpatialCutoff b q:ℂ)*
      (normalizedFullDensity B rootB phi hphi d P.T (fun y=>P.V (J.W y)) (complexify m q)-1)‖≤
        truncatedExponential (2*K*(2*Real.pi^2+1)) L
          (c.re*constrainedSquaredRadius q/tau (m+1)) := by
  let c := H/((2*(m+1:ℕ):ℝ):ℂ)
  let x := c.re*constrainedSquaredRadius q/tau (m+1)
  have hn : (0:ℝ)<(m+1:ℕ) := by positivity
  have ht := tau_pos (m+1) (by omega)
  have hc : 0<c.re := by
    dsimp [c]
    rw [Complex.div_ofReal_re]
    exact div_pos (by linarith) (by positivity)
  have hx : 0≤x := div_nonneg (mul_nonneg hc.le (constrainedSquaredRadius_nonneg q)) ht.le
  have hC : 0≤2*K*(2*Real.pi^2+1) := by positivity
  apply cutoff_exponential_bound _ _ x _ _ hC hx
  · rw [Real.norm_of_nonneg (show 0≤shapeSpatialCutoff b q from b.nonneg)]
    exact b.le_one
  · intro hq
    have hQ : constrainedSquaredRadius q<b.rOut := by
      by_contra h
      exact hq (shapeSpatialCutoff_zero b (le_of_not_gt h))
    have hle : x<c.re*b.rOut/tau (m+1) := by dsimp [x]; gcongr
    linarith
  · intro hq
    have hu := cutoff_freeChart_lt b delta hdelta hb q hq
    have he := hfull (complexify m q) hu
    rw [realFreeChart_absoluteEnergy] at he
    have hs := beta_coordinate_energy_control (m+1:ℕ) (tau (m+1)) H.re
      (constrainedSquaredRadius q) hn ht hH (constrainedSquaredRadius_nonneg q)
      (scaled_tau_bounds (m+1) (by omega)).2
    have hscale : (m+1:ℕ)*constrainedSquaredRadius q≤(2*Real.pi^2)*x := by
      simpa only [x,c,Complex.div_ofReal_re] using hs
    apply he.trans
    exact density_energy_to_exponential _ x (2*Real.pi^2) K (mul_nonneg (by positivity) (constrainedSquaredRadius_nonneg q)) hx
      (by positivity) hK hscale

end
end IsingBulk.Anisotropic.NegativeNormalForm
