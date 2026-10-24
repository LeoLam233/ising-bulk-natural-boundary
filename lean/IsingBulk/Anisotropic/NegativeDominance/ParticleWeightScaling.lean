import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedPeriod

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges MeasureTheory
open scoped BigOperators

theorem edgeNumerator_div_scale {N : ℕ} (b : ℝ) (B S A : ℂ → ℂ)
    (u : ℂ) (q : Fin N → ℝ) :
    edgeNumerator b B (fun v => S v/A v) u (List.ofFn q)=
      (A u)^N*edgeNumerator b B S u (List.ofFn q) := by
  rw [edgeNumerator_eq_indexed,edgeNumerator_eq_indexed]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
  ring

theorem edgeFullIntegrand_div_scale {N : ℕ} (b : ℝ) (B S A : ℂ → ℂ)
    (u : ℂ) (q : Fin N → ℝ) :
    edgeFullIntegrand b B (fun v => S v/A v) u q=
      (A u)^N*edgeFullIntegrand b B S u q := by
  unfold edgeFullIntegrand
  rw [edgeNumerator_div_scale]
  ring

theorem negativeShiftedFullIntegrand_div_scale (b : ℝ) (B S A : ℂ → ℂ)
    (n : ℕ) (u : ℂ) (q : Fin n → ℝ) :
    negativeShiftedFullIntegrand b B (fun v => S v/A v) n u q=
      (A u)^(n+1)*negativeShiftedFullIntegrand b B S n u q :=
  edgeFullIntegrand_div_scale b B S A u (negativeShiftedAngles n q)

theorem negativeShiftedPeriod_div_scale (b : ℝ) (B S A : ℂ → ℂ)
    (n : ℕ) (u : ℂ) :
    negativeShiftedPeriod b B (fun v => S v/A v) n u=
      (A u)^(n+1)*negativeShiftedPeriod b B S n u := by
  unfold negativeShiftedPeriod
  simp_rw [negativeShiftedFullIntegrand_div_scale]
  rw [integral_const_mul]
  ring

/-- Exact integer particle weights; the residual square root is one common
analytic factor, not an index-dependent normalization discarded from estimates. -/
theorem weighted_fullCoefficient_eq_scaledPeriod (n : ℕ)
    {lam b : ℝ} {B S A : ℂ → ℂ} {z u : ℂ} (hlam : 0<lam)
    (hz : z∈omegaH lam\{0})
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (hA : (A u)^2=spectralProduct lam z) (hA0 : A u≠0) :
    spectralProduct lam z^n*FormFactors.unscaledFullCoefficient (2*n+1) lam z=
      (A u)⁻¹*negativeShiftedPeriod b B (fun v => S v/A v) (2*n) u := by
  rw [negativeShiftedPeriod_div_scale,unscaledFullCoefficient_eq_negativeShiftedPeriod
    (2*n) hlam hz hB hS he hu hBi,pow_succ,pow_mul,hA]
  field_simp

end
end IsingBulk.Anisotropic.NegativeDominance
