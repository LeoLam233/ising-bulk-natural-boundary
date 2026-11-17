import IsingBulk.AnisoF002.Isotropic.JointInverse

/-!
# Curvature of the actual joint isotropic inverse

This file differentiates the analytic inverse constructed in `JointInverse`.
The positive curvature is a local input to frozen F002 Lemma 7.3 and the
filled secant in equation `eq:iso-covariance-field`.  It does not assume a
second derivative formula as a hypothesis.  The common neighborhood of the
entire one-sided arc and the physical occupancy/coarea estimate remain
separate obligations.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter

/-- The exact curvature expression obtained by differentiating the original
dispersion twice, using the unsquared inverse denominator. -/
def inverseCurvature (S w φ : ℂ) : ℂ :=
  S * (1 - Complex.cos w * Complex.cos φ) /
    (Complex.sin φ - Complex.sin w) ^ 3

/-- The trigonometric numerator is the positive-real curvature numerator on
the physical right arc. -/
theorem inverse_curvature_numerator (w φ S : ℂ)
    (hdisp : Complex.cos w + Complex.cos φ = S) :
    Complex.cos φ * Complex.sin w ^ 2 + Complex.cos w * Complex.sin φ ^ 2 =
      S * (1 - Complex.cos w * Complex.cos φ) := by
  rw [← hdisp]
  linear_combination
    Complex.cos φ * Complex.sin_sq_add_cos_sq w +
    Complex.cos w * Complex.sin_sq_add_cos_sq φ

/-- This is the second derivative of an actual analytic local solution of
the original dispersion, not a definition substituted for that derivative. -/
theorem inverse_coordinate_second_derivative (U : ℂ → ℂ) (S v : ℂ)
    (hU : AnalyticAt ℂ U v)
    (hdisp : (fun z => Complex.cos (U z) + Complex.cos (z - U z)) =ᶠ[𝓝 v]
      (fun _ => S))
    (hden : Complex.sin (v - U v) - Complex.sin (U v) ≠ 0) :
    HasDerivAt (deriv U) (inverseCurvature S (U v) (v - U v)) v := by
  have hu : HasDerivAt U
      (Complex.sin (v - U v) / (Complex.sin (v - U v) - Complex.sin (U v))) v := by
    have hd := hU.differentiableAt.hasDerivAt
    have he := inverse_coordinate_derivative U S v _ hd hdisp hden
    simpa only [he] using hd
  have hφ := (hasDerivAt_id v).sub hu
  have hn := hφ.csin
  have hd := hn.sub hu.csin
  have hquot := hn.div hd hden
  have hne : ∀ᶠ z in 𝓝 v,
      Complex.sin (z - U z) - Complex.sin (U z) ≠ 0 :=
    hd.continuousAt.eventually_ne hden
  have hform : deriv U =ᶠ[𝓝 v]
      (fun z => Complex.sin (z - U z) /
        (Complex.sin (z - U z) - Complex.sin (U z))) := by
    filter_upwards [hU.eventually_analyticAt, hdisp.eventually_nhds, hne]
      with z haz hez hnz
    exact inverse_coordinate_derivative U S z _ haz.differentiableAt.hasDerivAt hez hnz
  have hc :
      ((Complex.cos (v - U v) *
          (1 - Complex.sin (v - U v) /
            (Complex.sin (v - U v) - Complex.sin (U v)))) *
          (Complex.sin (v - U v) - Complex.sin (U v)) -
        Complex.sin (v - U v) *
          (Complex.cos (v - U v) *
              (1 - Complex.sin (v - U v) /
                (Complex.sin (v - U v) - Complex.sin (U v))) -
            Complex.cos (U v) * (Complex.sin (v - U v) /
              (Complex.sin (v - U v) - Complex.sin (U v))))) /
        (Complex.sin (v - U v) - Complex.sin (U v)) ^ 2 =
      (Complex.cos (v - U v) * Complex.sin (U v) ^ 2 +
        Complex.cos (U v) * Complex.sin (v - U v) ^ 2) /
        (Complex.sin (v - U v) - Complex.sin (U v)) ^ 3 := by
    field_simp [hden]
    ring
  have hnum := inverse_curvature_numerator (U v) (v - U v) S hdisp.self_of_nhds
  convert hquot.congr_of_eventuallyEq hform using 1
  simpa only [inverseCurvature, hnum, Pi.sub_apply, id_eq] using hc.symm

/-- The joint inverse supplies the genuine second coordinate derivative on
each local parameter slice. -/
theorem joint_inverse_coordinate_second_derivative
    (U : (ℂ × ℂ) → ℂ) (S v : ℂ) (hU : AnalyticAt ℂ U (S, v))
    (hdisp : ∀ᶠ q in 𝓝 (S, v),
      Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1)
    (hden : Complex.sin (v - U (S, v)) - Complex.sin (U (S, v)) ≠ 0) :
    HasDerivAt (deriv (fun z => U (S, z)))
      (inverseCurvature S (U (S, v)) (v - U (S, v))) v := by
  apply inverse_coordinate_second_derivative
    (fun z => U (S, z)) S v (hU.comp (analyticAt_const.prod analyticAt_id)) _ hden
  exact (continuousAt_const.prodMk continuousAt_id).eventually hdisp

/-- The actual curvature formula is jointly analytic wherever the actual
inverse is analytic and its unsquared denominator is nonzero. -/
theorem joint_inverseCurvature_analyticAt
    (U : (ℂ × ℂ) → ℂ) (q : ℂ × ℂ) (hU : AnalyticAt ℂ U q)
    (hden : Complex.sin (q.2 - U q) - Complex.sin (U q) ≠ 0) :
    AnalyticAt ℂ (fun z => inverseCurvature z.1 (U z) (z.2 - U z)) q := by
  unfold inverseCurvature
  exact (analyticAt_fst.mul
    (analyticAt_const.sub ((Complex.analyticAt_cos.comp hU).mul
      (Complex.analyticAt_cos.comp (analyticAt_snd.sub hU))))).div
    (((Complex.analyticAt_sin.comp (analyticAt_snd.sub hU)).sub
      (Complex.analyticAt_sin.comp hU)).pow 3) (pow_ne_zero _ hden)

/-- The real curvature numerator controls the square of the unsquared
denominator without an explicit arccosine branch choice. -/
theorem real_inverse_curvature_gap (w φ : ℝ) :
    (Real.sin φ - Real.sin w) ^ 2 ≤
      4 * (1 - Real.cos w * Real.cos φ) := by
  have hw := Real.sin_sq_add_cos_sq w
  have hφ := Real.sin_sq_add_cos_sq φ
  nlinarith [sq_nonneg (Real.sin φ + Real.sin w),
    sq_nonneg (Real.cos w - Real.cos φ)]

/-- Strict positive curvature on the physical right-arc orientation. -/
theorem real_inverse_curvature_pos (S w φ : ℝ)
    (hS : 0 < S) (hden : 0 < Real.sin φ - Real.sin w) :
    0 < S * (1 - Real.cos w * Real.cos φ) /
      (Real.sin φ - Real.sin w) ^ 3 := by
  have hgap : 0 < 1 - Real.cos w * Real.cos φ := by
    have h := real_inverse_curvature_gap w φ
    nlinarith [sq_pos_of_pos hden]
  exact div_pos (mul_pos hS hgap) (pow_pos hden _)

/-- A quantitative lower bound, suitable for compact right-arc coverage. -/
theorem real_inverse_curvature_lower_bound (S w φ : ℝ)
    (hS : 0 ≤ S) (hden : 0 < Real.sin φ - Real.sin w) :
    S / (4 * (Real.sin φ - Real.sin w)) ≤
      S * (1 - Real.cos w * Real.cos φ) /
        (Real.sin φ - Real.sin w) ^ 3 := by
  apply (div_le_div_iff₀ (by positivity) (pow_pos hden _)).2
  have h := mul_le_mul_of_nonneg_left (real_inverse_curvature_gap w φ) hS
  nlinarith [mul_nonneg (by positivity : 0 ≤ Real.sin φ - Real.sin w)
    (sub_nonneg.mpr h)]

/-- At every physical right-arc point with the correct orientation, the
constructed inverse has genuinely positive second coordinate derivative on
a joint complex neighborhood.  The second derivative is supplied as a
`HasDerivAt` fact at every point of that neighborhood. -/
theorem exists_joint_inverse_positive_curvature (w φ : ℝ)
    (hS : 0 < Real.cos w + Real.cos φ)
    (hden : 0 < Real.sin φ - Real.sin w) :
    ∃ (U : (ℂ × ℂ) → ℂ) (c : ℝ), 0 < c ∧
      AnalyticAt ℂ U (Complex.cos w + Complex.cos φ, (w : ℂ) + φ) ∧
      U (Complex.cos w + Complex.cos φ, (w : ℂ) + φ) = w ∧
      ∀ᶠ q in 𝓝 (Complex.cos w + Complex.cos φ, (w : ℂ) + φ),
        Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1 ∧
        HasDerivAt (deriv (fun z => U (q.1, z)))
          (inverseCurvature q.1 (U q) (q.2 - U q)) q.2 ∧
        c ≤ (inverseCurvature q.1 (U q) (q.2 - U q)).re := by
  have hdenC : Complex.sin (φ : ℂ) - Complex.sin (w : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_sin, ← Complex.ofReal_sub]
    exact_mod_cast ne_of_gt hden
  obtain ⟨U, hU, hvalue, hdisp⟩ := exists_joint_analytic_inverse w φ hdenC
  let q₀ : ℂ × ℂ := (Complex.cos w + Complex.cos φ, (w : ℂ) + φ)
  let K : (ℂ × ℂ) → ℂ := fun q => inverseCurvature q.1 (U q) (q.2 - U q)
  have hD : Complex.sin (q₀.2 - U q₀) - Complex.sin (U q₀) ≠ 0 := by
    simpa only [q₀, hvalue, add_sub_cancel_left] using hdenC
  have hK : AnalyticAt ℂ K q₀ := joint_inverseCurvature_analyticAt U q₀ hU hD
  have hKvalue : (K q₀).re =
      (Real.cos w + Real.cos φ) * (1 - Real.cos w * Real.cos φ) /
        (Real.sin φ - Real.sin w) ^ 3 := by
    dsimp only [K, q₀]
    rw [hvalue, add_sub_cancel_left]
    unfold inverseCurvature
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sin]
    norm_cast
  have hKpos : 0 < (K q₀).re := by
    rw [hKvalue]
    exact real_inverse_curvature_pos _ _ _ hS hden
  have hhalf : (K q₀).re / 2 < (K q₀).re := by linarith
  have hpos : ∀ᶠ q in 𝓝 q₀, (K q₀).re / 2 < (K q).re :=
    (Complex.continuous_re.continuousAt.comp hK.continuousAt).eventually
      (lt_mem_nhds hhalf)
  have hne : ∀ᶠ q in 𝓝 q₀,
      Complex.sin (q.2 - U q) - Complex.sin (U q) ≠ 0 := by
    have hcont : ContinuousAt
        (fun q : ℂ × ℂ => Complex.sin (q.2 - U q) - Complex.sin (U q)) q₀ :=
      (Complex.continuous_sin.continuousAt.comp
        (continuousAt_snd.sub hU.continuousAt)).sub
        (Complex.continuous_sin.continuousAt.comp hU.continuousAt)
    exact hcont.eventually_ne hD
  refine ⟨U, (K q₀).re / 2, by positivity, hU, hvalue, ?_⟩
  filter_upwards [hU.eventually_analyticAt, hdisp.eventually_nhds, hpos, hne]
    with q hUq hdq hpq hnq
  refine ⟨hdq.self_of_nhds, ?_, hpq.le⟩
  exact joint_inverse_coordinate_second_derivative U q.1 q.2 hUq hdq hnq

end IsingBulk.AnisoF002.Isotropic
