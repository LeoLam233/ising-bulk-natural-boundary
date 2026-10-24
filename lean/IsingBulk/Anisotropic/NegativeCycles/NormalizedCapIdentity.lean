import IsingBulk.Anisotropic.NegativeCycles.ActualIntegralTransport
import IsingBulk.Anisotropic.NegativeCycles.ModelTail
import IsingBulk.Anisotropic.NegativeNormalForm.FullDensityDomain
import IsingBulk.Anisotropic.NegativeNormalForm.UniformExactNormalForm

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric
open scoped BigOperators

/-- Exact normalized cap identity, including the full constrained Jacobian and
all coincidence divisors. No division by a Vandermonde is used. -/
theorem normalized_cap_pointwise {n : ℕ} (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (T : Config (n+1)→ℂ)
    (Phi : Config (n+1)→Config (n+1)) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀e v,Phi (permute e v)=permute e (Phi v))
    (hcenter : regularResidue B rootB phi hphi d T 0≠0)
    (q : Fin n→ℝ) (hq : ‖freeChartCLM n (complexify n q)‖<r)
    (hm : ZeroMean (Phi (freeChartCLM n (complexify n q))))
    (τ : ℝ) (c : ℂ)
    (hT : T (Phi (freeChartCLM n (complexify n q)))=(τ:ℂ)+c*(constrainedSquaredRadius q:ℂ))
    (j : ℕ) :
    constrainedResidueDensity B rootB phi hphi d T j
        (constrainedMap Phi (complexify n q))*constrainedJacobian Phi (complexify n q)=
      regularResidue B rootB phi hphi d T 0*
        normalizedFullDensity B rootB phi hphi d T Phi (complexify n q)*
        quadraticModelKernel n j τ c q := by
  rw [constrainedResidueDensity_pullback B rootB phi hphi d T j Phi _ hm,
    poleResidue_full_pullback_on_ball B rootB phi hphi d T Phi r hPhi heq _ hq,hT]
  have hv : vandermonde (freeChartCLM n (complexify n q))=(firstVandermonde (shapeExtend q):ℂ) := by
    rw [freeChartCLM_eq_shapeExtend,shapeExtend_complexify]
    simp [vandermonde,firstVandermonde]
  rw [hv]
  unfold normalizedFullDensity quadraticModelKernel
  rw [mul_div_cancel₀ _ hcenter]
  ring

/-- The exact quadratic denominator is obtained from the actual corrected
inverse witness, rather than assumed as a density approximation. -/
theorem corrected_normalized_cap_pointwise {n : ℕ} (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℝ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi (n+1) (d:ℂ) r C)
    (J : UniformCorrectionWitness B phi hphi (n+1) (d:ℂ) r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2)
    (hcenter : regularResidue B rootB phi hphi (d:ℂ) P.T 0≠0)
    (hh : centralHessian B phi (d:ℂ)≠0)
    (q : Fin n→ℝ) (hq : ‖freeChartCLM n (complexify n q)‖<R/2)
    (ha : phaseParameterQuotient B phi hphi (d:ℂ)
      (P.T (P.V (J.W (freeChartCLM n (complexify n q)))))≠0) (j : ℕ) :
    let Phi := fun y=>P.V (J.W y)
    constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
        (constrainedMap Phi (complexify n q))*constrainedJacobian Phi (complexify n q)=
      regularResidue B rootB phi hphi (d:ℂ) P.T 0*
        normalizedFullDensity B rootB phi hphi (d:ℂ) P.T Phi (complexify n q)*
        quadraticModelKernel n j (1-Real.cos d)
          (centralHessian B phi (d:ℂ)/(2*(n+1:ℕ))) q := by
  dsimp only
  have he := J.exact_energy (Nat.succ_ne_zero n) B phi hphi (d:ℂ) r C R P hr hRr
    (freeChartCLM n (complexify n q)) hq.le (by rw [freeChartCLM_eq_shapeExtend]; exact sum_shapeExtend _) hh ha
  apply normalized_cap_pointwise B rootB phi hphi (d:ℂ) P.T (fun y=>P.V (J.W y))
    (R/2) (J.corrected_bounds B phi hphi (d:ℂ) r C R P hr hR hRr).1
    (fun e v=>by rw [J.w_perm,P.v_perm]) hcenter q hq he.1 _ _ ?_ j
  rw [he.2,freeChartCLM_eq_shapeExtend,shapeExtend_complexify]
  have hquad : (∑i, ((shapeExtend q i:ℝ):ℂ)^2)=(constrainedSquaredRadius q:ℂ) := by
    simp only [constrainedSquaredRadius,squaredRadius,Complex.ofReal_sum,Complex.ofReal_pow]
  simp only [quadratic,hquad,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_cos]

end IsingBulk.Anisotropic.NegativeCycles
