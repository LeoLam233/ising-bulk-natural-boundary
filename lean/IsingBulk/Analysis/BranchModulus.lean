import IsingBulk.Analysis.BranchCurrentTaylor

/-! Two-sided modulus estimates, retaining a quadratic real center shift. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem modulus_of_component_bounds (z : ℂ) (u q a b C K : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) (hK : 0 < K)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hu1 : |u| ≤ 1) (hku : K*|u| ≤ a/2)
    (hr : |z.re-a*u| ≤ K*(u^2+q^2))
    (hi : b*q ≤ -z.im) (hi' : -z.im ≤ C*q) :
    (a*b/(a+2*b+2*K))*(|u|+q) ≤ ‖z‖ ∧
      ‖z‖ ≤ (a+2*K+C)*(|u|+q) := by
  have hqnorm : b*q ≤ ‖z‖ := hi.trans ((neg_le_abs _).trans (Complex.abs_im_le_norm z))
  have hquad : K*u^2 ≤ a/2*|u| := by nlinarith [mul_le_mul_of_nonneg_right hku (abs_nonneg u),sq_abs u]
  have hquadq : K*q^2 ≤ K*q := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1)]
  have hreu : a*|u| ≤ |z.re|+|z.re-a*u| := by
    have h := abs_sub_le (a*u) z.re 0
    simpa [abs_mul,abs_of_pos ha,abs_sub_comm,add_comm] using h
  have hbound : a/2*|u| ≤ ‖z‖+K*q := by
    nlinarith [Complex.abs_re_le_norm z]
  have hl : a*b*(|u|+q) ≤ (a+2*b+2*K)*‖z‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hbound hb.le,
      mul_le_mul_of_nonneg_left hqnorm hK.le,mul_le_mul_of_nonneg_left hqnorm ha.le]
  constructor
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity : 0 < a+2*b+2*K)).mpr (by simpa [mul_comm] using hl)
  · have hrea : |z.re| ≤ a*|u|+K*(u^2+q^2) := by
      have h := abs_sub_le z.re (a*u) 0
      simp only [sub_zero,abs_mul,abs_of_pos ha] at h
      linarith
    have hima : |z.im| ≤ C*q := by
      rw [abs_of_nonpos (by nlinarith : z.im ≤ 0)]
      exact hi'
    have huq : u^2 ≤ |u| := by nlinarith [sq_abs u,mul_nonneg (abs_nonneg u) (sub_nonneg.mpr hu1)]
    have hqq : q^2 ≤ q := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1)]
    have hn := Complex.norm_le_abs_re_add_abs_im z
    nlinarith [mul_le_mul_of_nonneg_left huq hK.le,mul_le_mul_of_nonneg_left hqq hK.le,
      mul_nonneg ha.le hq,mul_nonneg hC.le (abs_nonneg u),
      mul_nonneg hK.le hq,mul_nonneg hK.le (abs_nonneg u)]

theorem current_modulus_Q (d : LocalBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      c*(|u|+ε+d.tau*t) ≤ ‖currentD d ε t u‖ ∧
        ‖currentD d ε t u‖ ≤ C*(|u|+ε+d.tau*t) := by
  obtain ⟨K,r₁,hK,hr₁,hreal⟩ := current_real_remainder d
  obtain ⟨b,C,r₂,hb,hC,hr₂,himag⟩ := current_imaginary_margin d
  let r := min r₁ (min r₂ (min (1/(2*(1+d.tau))) (min 1 (d.a/(2*K)))))
  have ha := d.a_pos
  have hτ := d.tau_pos
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨d.a*b/(d.a+2*b+2*K),d.a+2*K+C,r,by positivity,by positivity,hr,?_⟩
  intro ε t u hε hεr ht htr hur
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hrrτ : r ≤ 1/(2*(1+d.tau)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrr1 : r ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrra : r ≤ d.a/(2*K) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hQ1 : ε+d.tau*t ≤ 1 := by
    have hx := (le_div_iff₀ (by positivity : 0 < 2*(1+d.tau))).mp hrrτ
    nlinarith [mul_lt_mul_of_pos_left htr hτ]
  have hku : K*|u| ≤ d.a/2 := by
    have hx := (le_div_iff₀ (by positivity : 0 < 2*K)).mp hrra
    nlinarith [mul_lt_mul_of_pos_left hur hK]
  have hre := hreal ε t u hε.le (hεr.trans_le hrr₁) ht (htr.trans_le hrr₁) (hur.trans_le hrr₁)
  obtain ⟨hi,hi'⟩ := himag ε t u hε (hεr.trans_le hrr₂) ht (htr.trans_le hrr₂) (hur.trans_le hrr₂)
  have he : -(currentD d ε t u).im = (currentW d ε t u).im := by simp [currentD]
  rw [← he] at hi hi'
  simpa only [add_assoc] using modulus_of_component_bounds (currentD d ε t u) u
    (ε+d.tau*t) d.a b C K ha hb hC hK (by positivity) hQ1
    (hur.le.trans hrr1) hku hre hi hi'

end
end IsingBulk.Branch
