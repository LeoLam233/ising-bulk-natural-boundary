import IsingBulk.AnisoF002.C03.IsotropicImaginaryPeriodLimit

/-!
# Both physical parities of the genuine isotropic scalar period

The exact integer and half-integer evaluations at purely imaginary
curvature follow from a proved full-plane dominated limit.  Their
nonvanishing includes the independent-coordinate Jacobian and the
principal square-root phase required by the frozen F002 proof.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem quadrantCurvature_ne_zero {D : ℝ} (hD : 0 < D) (eps : ℝ) :
    quadrantCurvature D eps ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp [quadrantCurvature] at hh
  exact hD.ne' hh

theorem continuous_quadrantCurvature (D : ℝ) : Continuous (quadrantCurvature D) := by
  unfold quadrantCurvature
  fun_prop

theorem integral_imaginary_quadraticPeriod_integer {d α : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (m : ℕ) {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) :
    (∫ v, quadraticPeriodIntegrand d (α + m + 1) τ (quadrantCurvature D 0) v
      ∂independentMeasure d) =
      (constrainedGaussianIntegral d : ℂ) * (m.factorial : ℂ) /
        (((α + m).factorial : ℂ) * (quadrantCurvature D 0) ^ α *
          (τ : ℂ) ^ (m + 1)) := by
  have hi := quadraticPeriod_integer_integrable hd hα m hτ
    (show (0 : ℝ) < (D : ℂ).re by simpa using hD)
  have hlim := quadrant_period_integral_limit hτ hD hi
  have hzero := quadrantCurvature_ne_zero hD 0
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hf : ((α + m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hc : ContinuousAt (fun eps : ℝ =>
      (constrainedGaussianIntegral d : ℂ) * (m.factorial : ℂ) /
        (((α + m).factorial : ℂ) * (quadrantCurvature D eps) ^ α *
          (τ : ℂ) ^ (m + 1))) 0 := by
    apply ContinuousAt.div continuousAt_const
    · exact ((continuousAt_const.mul ((continuous_quadrantCurvature D).continuousAt.pow α)).mul
        continuousAt_const)
    · exact mul_ne_zero (mul_ne_zero hf (pow_ne_zero _ hzero)) (pow_ne_zero _ hτ0)
  have heq : (fun eps : ℝ => ∫ v,
      quadraticPeriodIntegrand d (α + m + 1) τ (quadrantCurvature D eps) v
        ∂independentMeasure d) =ᶠ[𝓝[>] 0]
      (fun eps => (constrainedGaussianIntegral d : ℂ) * (m.factorial : ℂ) /
        (((α + m).factorial : ℂ) * (quadrantCurvature D eps) ^ α *
          (τ : ℂ) ^ (m + 1))) := by
    filter_upwards [self_mem_nhdsWithin] with eps he
    exact integral_quadraticPeriod_integer hd hα m hτ
      (by simpa only [quadrantCurvature_re, Set.mem_Ioi] using he)
  exact tendsto_nhds_unique hlim
    ((tendsto_congr' heq).2 (hc.tendsto.mono_left nhdsWithin_le_nhds))

theorem imaginary_quadraticPeriod_integer_ne_zero {d α : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (m : ℕ) {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) :
    (∫ v, quadraticPeriodIntegrand d (α + m + 1) τ (quadrantCurvature D 0) v
      ∂independentMeasure d) ≠ 0 := by
  rw [integral_imaginary_quadraticPeriod_integer hd hα m hτ hD]
  apply div_ne_zero
  · exact mul_ne_zero (by exact_mod_cast (constrainedGaussianIntegral_pos d).ne')
      (by exact_mod_cast Nat.factorial_ne_zero m)
  · exact mul_ne_zero
      (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (α + m))
        (pow_ne_zero _ (quadrantCurvature_ne_zero hD 0)))
      (pow_ne_zero _ (by exact_mod_cast hτ.ne'))

theorem integral_imaginary_quadraticPeriod_half_integer {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    (∫ v, quadraticPeriodIntegrand d (a + 1) τ (quadrantCurvature D 0) v
      ∂independentMeasure d) =
      (constrainedGaussianIntegral d : ℂ) * (Real.sqrt Real.pi : ℂ) *
        Complex.sqrt (quadrantCurvature D 0) /
      ((a.factorial : ℂ) * (quadrantCurvature D 0) ^ (a + 1) * (Real.sqrt τ : ℂ)) := by
  have hi := quadraticPeriod_half_integer_integrable hd ha hτ
    (show (0 : ℝ) < (D : ℂ).re by simpa using hD)
  have hlim := quadrant_period_integral_limit hτ hD hi
  have hzero := quadrantCurvature_ne_zero hD 0
  have hsτ : (Real.sqrt τ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hτ).ne'
  have hf : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hsqrt : ContinuousAt (fun eps : ℝ => Complex.sqrt (quadrantCurvature D eps)) 0 :=
    (Complex.continuousAt_sqrt (Or.inl (by simp only [quadrantCurvature_re]; exact le_rfl))).comp
      (continuous_quadrantCurvature D).continuousAt
  have hc : ContinuousAt (fun eps : ℝ =>
      (constrainedGaussianIntegral d : ℂ) * (Real.sqrt Real.pi : ℂ) *
        Complex.sqrt (quadrantCurvature D eps) /
      ((a.factorial : ℂ) * (quadrantCurvature D eps) ^ (a + 1) * (Real.sqrt τ : ℂ))) 0 := by
    apply ContinuousAt.div (continuousAt_const.mul hsqrt)
    · exact (continuousAt_const.mul ((continuous_quadrantCurvature D).continuousAt.pow _)).mul
        continuousAt_const
    · exact mul_ne_zero (mul_ne_zero hf (pow_ne_zero _ hzero)) hsτ
  have heq : (fun eps : ℝ => ∫ v,
      quadraticPeriodIntegrand d (a + 1) τ (quadrantCurvature D eps) v
        ∂independentMeasure d) =ᶠ[𝓝[>] 0]
      (fun eps => (constrainedGaussianIntegral d : ℂ) * (Real.sqrt Real.pi : ℂ) *
        Complex.sqrt (quadrantCurvature D eps) /
      ((a.factorial : ℂ) * (quadrantCurvature D eps) ^ (a + 1) * (Real.sqrt τ : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with eps he
    exact integral_quadraticPeriod_half_integer_sqrt hd ha hτ
      (by simpa only [quadrantCurvature_re, Set.mem_Ioi] using he)
  exact tendsto_nhds_unique hlim
    ((tendsto_congr' heq).2 (hc.tendsto.mono_left nhdsWithin_le_nhds))

theorem imaginary_quadraticPeriod_half_integer_ne_zero {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    (∫ v, quadraticPeriodIntegrand d (a + 1) τ (quadrantCurvature D 0) v
      ∂independentMeasure d) ≠ 0 := by
  rw [integral_imaginary_quadraticPeriod_half_integer hd ha hτ hD]
  have hz := quadrantCurvature_ne_zero hD 0
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (by exact_mod_cast (constrainedGaussianIntegral_pos d).ne')
        (by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'))
      (complex_sqrt_ne_zero hz)
  · exact mul_ne_zero
      (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero a) (pow_ne_zero _ hz))
      (by exact_mod_cast (Real.sqrt_pos.2 hτ).ne')

end
end IsingBulk.AnisoF002.NegativeHT.Angular
