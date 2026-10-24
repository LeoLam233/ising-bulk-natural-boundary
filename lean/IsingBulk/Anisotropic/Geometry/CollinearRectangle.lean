import IsingBulk.Anisotropic.Geometry.CoordinateAlgebra

namespace IsingBulk.Anisotropic
noncomputable section

/-- A collinear rectangle is its exact unsquared real segment, not a squared surrogate. -/
theorem collinear_rectangle_representation (a b A : ℂ) (ha : a.re ≠ 0)
    (hd : a.re*b.im-a.im*b.re=0) (hN : a.re*A.im-a.im*A.re=0)
    (hn : ‖A‖ ≤ ‖a‖+‖b‖) :
    ∃ u∈Set.Icc (-1:ℝ) 1, ∃ v∈Set.Icc (-1:ℝ) 1, A=a*(u:ℂ)+b*(v:ℂ) := by
  let r : ℝ := b.re/a.re
  let w : ℝ := A.re/a.re
  have hb : b=a*(r:ℂ) := by
    apply Complex.ext
    · change b.re=a.re*(b.re/a.re)-a.im*0
      simp only [mul_zero,sub_zero]
      field_simp
    · change b.im=a.re*0+a.im*(b.re/a.re)
      simp only [mul_zero,zero_add]
      rw [← mul_div_assoc, eq_div_iff ha]
      nlinarith [hd]
  have hA : A=a*(w:ℂ) := by
    apply Complex.ext
    · change A.re=a.re*(A.re/a.re)-a.im*0
      simp only [mul_zero,sub_zero]
      field_simp
    · change A.im=a.re*0+a.im*(A.re/a.re)
      simp only [mul_zero,zero_add]
      rw [← mul_div_assoc, eq_div_iff ha]
      nlinarith [hN]
  have ha0 : a ≠ 0 := fun he => ha (by simp [he])
  have hnorm := norm_pos_iff.mpr ha0
  have hw : |w|≤1+|r| := by
    rw [hA,hb,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_eq_abs] at hn
    nlinarith
  let u := w/(1+|r|)
  have hk : 0<1+|r| := by positivity
  have hu : |u|≤1 := by
    dsimp [u]
    rw [abs_div,abs_of_pos hk,div_le_one₀ hk]
    exact hw
  by_cases hr : 0≤r
  · refine ⟨u,abs_le.mp hu,u,abs_le.mp hu,?_⟩
    have hw' : w=u+r*u := by
      dsimp [u]
      rw [abs_of_nonneg hr]
      rw [← mul_div_assoc, ← add_div, eq_div_iff (by linarith : 1+r ≠ 0)]
      ring
    rw [hA,hb,hw']
    push_cast
    ring
  · refine ⟨u,abs_le.mp hu,-u,abs_le.mp (by simpa using hu),?_⟩
    have hw' : w=u-r*u := by
      dsimp [u]
      rw [abs_of_neg (lt_of_not_ge hr)]
      rw [← mul_div_assoc, ← sub_div, eq_div_iff (by linarith : 1 + -r ≠ 0)]
      ring
    rw [hA,hb,hw']
    push_cast
    ring

/-- The dispersion identity and unit product yield the exact segment-length bound. -/
theorem dispersion_norm_bound (a b A : ℂ)
    (hA : A^2=(1+a^2)*(1+b^2)) (hp : ‖a*b‖=1) : ‖A‖≤‖a‖+‖b‖ := by
  have h1 := norm_add_le (1:ℂ) (a^2)
  rw [Complex.norm_pow, norm_one] at h1
  have h2 := norm_add_le (1:ℂ) (b^2)
  rw [Complex.norm_pow, norm_one] at h2
  have h3 : ‖A‖^2≤(1+‖a‖^2)*(1+‖b‖^2) := by
    calc
      ‖A‖^2=‖A^2‖ := (Complex.norm_pow _ _).symm
      _=‖1+a^2‖*‖1+b^2‖ := by rw [hA,norm_mul]
      _≤(1+‖a‖^2)*(1+‖b‖^2) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  rw [norm_mul] at hp
  have hp2 : ‖a‖^2*‖b‖^2=1 := by nlinarith [congrArg (fun x:ℝ => x^2) hp]
  nlinarith [norm_nonneg A,norm_nonneg a,norm_nonneg b]

end
end IsingBulk.Anisotropic
