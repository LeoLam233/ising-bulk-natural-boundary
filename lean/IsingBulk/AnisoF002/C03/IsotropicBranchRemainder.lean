import IsingBulk.AnisoF002.C03.IsotropicRadialApproach
import IsingBulk.AnisoF002.C03.NegativeDerivativeAverage

/-!
# Quantified real remainder in the actual lower-branch normal form

The quadratic remainder is derived from the checked generic analytic
Taylor estimate and the exact physical exterior radial parameter. Its
real nature is retained explicitly, separately from attenuation.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem analytic_scalar_quadratic_remainder (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ z : ℂ, ‖z‖ < r →
      ‖f z - f 0 - deriv f 0 * z‖ ≤ M * ‖z‖ ^ 2 := by
  let H : ℂ × ℂ → ℂ := fun p => f p.1
  have hH : AnalyticAt ℂ H (0, 0) := hf.comp (f := fun p : ℂ × ℂ => p.1) analyticAt_fst
  obtain ⟨r, M, hr, hM, _, _, hquad⟩ := NegativeHT.analytic_joint_uniform_estimates hH
  have hd : HasFDerivAt H (deriv f 0 • ContinuousLinearMap.fst ℂ ℂ ℂ) (0, 0) :=
    hf.differentiableAt.hasDerivAt.comp_hasFDerivAt (0, 0) (hasFDerivAt_fst (𝕜 := ℂ))
  refine ⟨r, M, hr, hM, ?_⟩
  intro z hz
  have hz' : (z, (0 : ℂ)) ∈ ball (0, 0) r := by
    simpa only [mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_def,
      norm_zero, max_eq_left (norm_nonneg z)] using hz
  have hh := hquad (0, 0) (mem_ball_self hr) (z, 0) hz'
  rw [hd.fderiv] at hh
  have hfst : (ContinuousLinearMap.fst ℂ ℂ ℂ) (z, 0) = z := rfl
  simpa only [H, Prod.mk_sub_mk, sub_zero, smul_apply, hfst,
    smul_eq_mul, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg z)] using hh

theorem exists_cos_branch_quadratic_remainder (b : ℝ) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ u : ℝ, |u| < r →
      |Real.cos (b - u) - Real.cos b - Real.sin b * u| ≤ M * u ^ 2 := by
  let f : ℂ → ℂ := fun z => Complex.cos ((b : ℂ) - z)
  have hf : AnalyticAt ℂ f 0 := Complex.analyticAt_cos.comp (analyticAt_const.sub analyticAt_id)
  obtain ⟨r, M, hr, hM, hrem⟩ := analytic_scalar_quadratic_remainder f hf
  have hd : HasDerivAt f (Real.sin b : ℂ) 0 := by
    simpa only [f, id_eq, sub_zero, neg_mul, mul_neg, mul_one, neg_neg, ← Complex.ofReal_sin] using
      (((hasDerivAt_id (0 : ℂ)).const_sub (b : ℂ)).ccos)
  refine ⟨r, M, hr, hM, ?_⟩
  intro u hu
  have hh := hrem (u : ℂ) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu)
  rw [hd.deriv] at hh
  have he : f (u : ℂ) - f 0 - (Real.sin b : ℂ) * (u : ℂ) =
      ((Real.cos (b - u) - Real.cos b - Real.sin b * u : ℝ) : ℂ) := by
    dsimp [f]
    push_cast
    simp only [sub_zero]
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
  exact hh

theorem exists_cosh_quadratic_remainder :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ h : ℝ, |h| < r →
      |Real.cosh h - 1| ≤ M * h ^ 2 := by
  obtain ⟨r, M, hr, hM, hrem⟩ := analytic_scalar_quadratic_remainder Complex.cosh
    Complex.analyticAt_cosh
  refine ⟨r, M, hr, hM, ?_⟩
  intro h hh
  have hb := hrem (h : ℂ) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hh)
  rw [(Complex.hasDerivAt_cosh 0).deriv] at hb
  simp only [Complex.cosh_zero, Complex.sinh_zero, zero_mul, sub_zero] at hb
  have he : Complex.cosh (h : ℂ) - 1 = ((Real.cosh h - 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
  exact hb

theorem isotropicDispersion_contour_re (S : ℂ) (θ h : ℝ) :
    (isotropicDispersion (S, (θ : ℂ) - Complex.I * (h : ℂ))).re =
      S.re - Real.cos θ * Real.cosh h := by
  have hw : (θ : ℂ) - Complex.I * (h : ℂ) = (θ : ℂ) + ((-h : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  unfold isotropicDispersion
  rw [hw, Complex.cos_add_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, Complex.sub_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
    sub_zero, Real.cosh_neg]

def branchRealRemainder (b : ℝ) (S : ℂ) (u h : ℝ) : ℝ :=
  Real.cos (b - u) * Real.cosh h - Real.cos b - Real.sin b * u - (S.re - (1 + Real.cos b))

def branchAttenuation (b : ℝ) (S : ℂ) (u h : ℝ) : ℝ :=
  S.im + Real.sinh h * Real.sin (b - u)

theorem isotropic_branch_normal_identity (b u h : ℝ) (S : ℂ) :
    1 - isotropicDispersion (S, ((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)) =
      ((Real.sin b * u + branchRealRemainder b S u h : ℝ) : ℂ) -
        Complex.I * (branchAttenuation b S u h : ℂ) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, isotropicDispersion_contour_re,
      branchRealRemainder, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    rw [show -b + u = -(b - u) by ring, Real.cos_neg]
    ring
  · simp only [Complex.sub_im, Complex.one_im, isotropicDispersion_contour_im,
      branchAttenuation, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add]
    rw [show -b + u = -(b - u) by ring, Real.sin_neg]
    ring

/-- The real remainder of the actual radial branch normal form is
uniformly quadratic in angular displacement, deformation, and epsilon. -/
theorem exists_isotropic_branch_real_remainder (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u h : ℝ, |u| < r → |h| < r →
        |branchRealRemainder b (isotropicRadialParameter α ε) u h| ≤
          C * (u ^ 2 + h ^ 2 + ε ^ 2) := by
  obtain ⟨r₁, M₁, hr₁, hM₁, hcos⟩ := exists_cos_branch_quadratic_remainder b
  obtain ⟨r₂, M₂, hr₂, hM₂, hcosh⟩ := exists_cosh_quadratic_remainder
  let r := min r₁ r₂
  let C := M₁ + M₂ + 1
  refine ⟨r, C, lt_min hr₁ hr₂, by dsimp [C]; positivity, ?_⟩
  intro ε hε hε1 u h hu hh
  have hc := hcos u (hu.trans_le (min_le_left _ _))
  have hch := hcosh h (hh.trans_le (min_le_right _ _))
  have hs := (isotropicRadialParameter_estimates α ε hα hε hε1).2.2.1
  have he : branchRealRemainder b (isotropicRadialParameter α ε) u h =
      (Real.cos (b - u) - Real.cos b - Real.sin b * u) +
        Real.cos (b - u) * (Real.cosh h - 1) -
          ((isotropicRadialParameter α ε).re - 2 * Real.cos α) := by
    unfold branchRealRemainder
    rw [hb]
    ring
  rw [he]
  have hprod : |Real.cos (b - u) * (Real.cosh h - 1)| ≤ M₂ * h ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) hch (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  dsimp [C]
  nlinarith [sq_nonneg u, sq_nonneg h, sq_nonneg ε]

end IsingBulk.AnisoF002.Isotropic
