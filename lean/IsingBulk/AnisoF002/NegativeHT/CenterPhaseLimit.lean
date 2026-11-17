import IsingBulk.AnisoF002.NegativeHT.HigherWindingRadial

/-!
# Phase control along the actual analytic center sequence

The local anisotropy factor B is evaluated at the exact centers
`1-cos(pi/n)`, not at a leading-order substitute.  Continuity at zero,
which the physical holomorphic factor will supply, discharges the uniform
boundedness premise in the preceding curvature estimates.  The resulting
phase comparison is uniform in every Taylor order.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open Filter
open scoped Topology

noncomputable section

theorem tendsto_windingTau_zero :
    Tendsto windingTau atTop (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => Real.pi/(n:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat Real.pi
  have hc : Tendsto (fun n : ℕ => Real.cos (Real.pi/(n:ℝ))) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def, Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.comp ht
  change Tendsto (fun n : ℕ => 1-Real.cos (Real.pi/(n:ℝ))) atTop (𝓝 (0:ℝ))
  simpa only [sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hc

/-- The genuine complex-valued analytic factor is evaluated at the
exact real center sequence. -/
theorem tendsto_anisotropy_at_centers (B : ℂ → ℂ) (hB : ContinuousAt B 0) :
    Tendsto (fun n : ℕ => B (windingTau n : ℂ)) atTop (𝓝 (B 0)) := by
  have ht : Tendsto (fun n : ℕ => (windingTau n : ℂ)) atTop (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_windingTau_zero
  exact hB.tendsto.comp ht

/-- Full eventual uniform phase estimate for B evaluated at the actual
centers.  No extra boundedness hypothesis on the center values remains. -/
theorem eventually_center_curvature_phase (B : ℂ → ℂ) (hB : ContinuousAt B 0)
    (b s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < (firstWindingCurvature n (B (windingTau n : ℂ)) b s).re ∧
      1 ≤ (‖firstWindingCurvature n (B (windingTau n : ℂ)) b s‖ /
        (firstWindingCurvature n (B (windingTau n : ℂ)) b s).re)^(particleExponent n) ∧
      (‖firstWindingCurvature n (B (windingTau n : ℂ)) b s‖ /
        (firstWindingCurvature n (B (windingTau n : ℂ)) b s).re)^(particleExponent n) ≤
        Real.exp (2*(curvatureErrorConstant (‖B 0‖+1) b s)^2/(n:ℝ)^2) := by
  have hb : ∀ᶠ n : ℕ in atTop, ‖B (windingTau n : ℂ)‖ ≤ ‖B 0‖+1 :=
    (tendsto_anisotropy_at_centers B hB).norm.eventually
      (eventually_le_nhds (by linarith))
  have hn2 : Tendsto (fun n : ℕ => (n:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp tendsto_natCast_atTop_atTop
  have hl : ∀ᶠ n : ℕ in atTop,
      2*curvatureErrorConstant (‖B 0‖+1) b s ≤ (n:ℝ)^2 :=
    hn2.eventually (eventually_ge_atTop _)
  filter_upwards [hb, hl, eventually_gt_atTop (0:ℕ)] with n hbn hln hn
  exact firstWindingCurvature_phase_uniform n (particleExponent n)
    (B (windingTau n : ℂ)) b s (‖B 0‖+1) hn (particleExponent_le_sq n) hbn hln

/-- The complete phase-cost ratio tends to one, even though the exponent
grows quadratically with particle number. -/
theorem tendsto_center_phase_ratio_one (B : ℂ → ℂ) (hB : ContinuousAt B 0)
    (b s : ℝ) :
    Tendsto (fun n : ℕ =>
      (‖firstWindingCurvature n (B (windingTau n : ℂ)) b s‖ /
        (firstWindingCurvature n (B (windingTau n : ℂ)) b s).re)^(particleExponent n))
      atTop (𝓝 (1:ℝ)) := by
  have he : Tendsto (fun n : ℕ =>
      2*(curvatureErrorConstant (‖B 0‖+1) b s)^2/(n:ℝ)^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by norm_num : (2:ℕ)≠0), mul_zero]
      using ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul
        (2*(curvatureErrorConstant (‖B 0‖+1) b s)^2)
  have he' : Tendsto (fun n : ℕ => Real.exp
      (2*(curvatureErrorConstant (‖B 0‖+1) b s)^2/(n:ℝ)^2)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp he
  have hc := eventually_center_curvature_phase B hB b s
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he'
    (hc.mono (fun _ hn => hn.2.1)) (hc.mono (fun _ hn => hn.2.2))

/-- The resulting comparison holds uniformly over every Taylor order
of the complete stored complex scalar model. -/
theorem eventually_center_model_phase (B : ℂ → ℂ) (hB : ContinuousAt B 0)
    (b s : ℝ) (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      ‖modelCoefficient n j (B (windingTau n : ℂ))
        (firstWindingCurvature n (B (windingTau n : ℂ)) b s) s (windingTau n)‖ ≤
      ‖modelCoefficient n j (B (windingTau n : ℂ))
        ((firstWindingCurvature n (B (windingTau n : ℂ)) b s).re : ℂ) s (windingTau n)‖ ∧
      ‖modelCoefficient n j (B (windingTau n : ℂ))
        ((firstWindingCurvature n (B (windingTau n : ℂ)) b s).re : ℂ) s (windingTau n)‖ ≤
      Real.exp (2*(curvatureErrorConstant (‖B 0‖+1) b s)^2/(n:ℝ)^2) *
        ‖modelCoefficient n j (B (windingTau n : ℂ))
          (firstWindingCurvature n (B (windingTau n : ℂ)) b s) s (windingTau n)‖ := by
  filter_upwards [eventually_center_curvature_phase B hB b s,
    eventually_gt_atTop (0:ℕ)] with n hc hn
  intro j
  rw [norm_modelCoefficient_realPart_curvature n j (B (windingTau n : ℂ))
    s (windingTau n) hn hs (windingTau_pos n hn) hc.1]
  constructor
  · simpa using mul_le_mul_of_nonneg_right hc.2.1
      (norm_nonneg (modelCoefficient n j (B (windingTau n : ℂ))
        (firstWindingCurvature n (B (windingTau n : ℂ)) b s) s (windingTau n)))
  · exact mul_le_mul_of_nonneg_right hc.2.2
      (norm_nonneg (modelCoefficient n j (B (windingTau n : ℂ))
        (firstWindingCurvature n (B (windingTau n : ℂ)) b s) s (windingTau n)))

end

end IsingBulk.AnisoF002.NegativeHT
