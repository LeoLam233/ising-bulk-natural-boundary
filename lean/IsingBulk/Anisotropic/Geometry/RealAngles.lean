import IsingBulk.Anisotropic.Geometry.SpectralSigns

namespace IsingBulk.Anisotropic
noncomputable section

private theorem real_angle_rectangle (h c H C t T u v : ℝ)
    (hh : 0<h) (hH : 0<H) (hcpos : 0<c) (hCpos : 0<C)
    (hc : c^2-h^2=1) (hC : C^2-H^2=1) (ht : t^2=1) (hT : T^2=1)
    (hu : |u|≤1) (hv : |v|≤1) (he : c*C*t*T=h*t*u+H*T*v) :
    C^2*t^2-c^2*H^2=0 ∧ c^2*T^2-h^2*C^2=0 := by
  have hat : |t|=1 := by nlinarith [sq_abs t, abs_nonneg t]
  have haT : |T|=1 := by nlinarith [sq_abs T, abs_nonneg T]
  have hbound : c*C ≤ h+H := by
    calc
      c*C = |c*C*t*T| := by rw [abs_mul,abs_mul,abs_mul,abs_of_pos hcpos,abs_of_pos hCpos,hat,haT]; ring
      _ = |h*t*u+H*T*v| := congrArg abs he
      _ ≤ |h*t*u|+|H*T*v| := abs_add_le _ _
      _ = h*|u|+H*|v| := by rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_pos hh,abs_of_pos hH,hat,haT]; ring
      _ ≤ h+H := by nlinarith [mul_le_mul_of_nonneg_left hu hh.le, mul_le_mul_of_nonneg_left hv hH.le]
  have hi : (c*C)^2-(h+H)^2=(h*H-1)^2 := by
    linear_combination C^2*hc+(h^2+1)*hC
  have hs := mul_self_le_mul_self (mul_pos hcpos hCpos).le hbound
  have hz : (h*H-1)^2=0 := by nlinarith [sq_nonneg (h*H-1)]
  have hp : h*H=1 := by linarith [sq_eq_zero_iff.mp hz]
  rw [ht,hT]
  constructor
  · linear_combination hC-H^2*hc-(h*H+1)*hp
  · linear_combination hc-h^2*hC-(h*H+1)*hp

/-- The simultaneous sine-zero degeneracy forces the unique corner root. -/
theorem signs_zero_of_mem_real_angles {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hx : 0<z.re) (hq : Real.sin z.im=0) (hQ : Real.sin (lam*z.im)=0)
    (hz : z ∈ spectralSet lam) : geometryF1 lam z.re z.im=0 ∧ geometryF2 lam z.re z.im=0 := by
  rcases hz with ⟨u,hu,v,hv,he⟩
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, spectralA_re, spectralS_re, spectralT_re, hq, hQ] at hre
  exact real_angle_rectangle _ _ _ _ _ _ u v
    (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hlam hx))
    (Real.cosh_pos _) (Real.cosh_pos _) (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _)
    (by simpa [hq] using Real.sin_sq_add_cos_sq z.im)
    (by simpa [hQ] using Real.sin_sq_add_cos_sq (lam*z.im))
    (abs_le.mpr hu) (abs_le.mpr hv) hre

theorem geometry_signs_of_mem_right {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hx : 0<z.re) (hz : z ∈ spectralSet lam) :
    geometryF1 lam z.re z.im*geometryF2 lam z.re z.im ≤ 0 := by
  by_cases hq : Real.sin z.im ≠ 0 ∨ Real.sin (lam*z.im) ≠ 0
  · exact (spectral_numerator_bounds_iff_signs hlam hx hq).mp (spectral_numerator_bounds_of_mem hz)
  · push Not at hq
    rw [(signs_zero_of_mem_real_angles hlam hx hq.1 hq.2 hz).1, zero_mul]

end
end IsingBulk.Anisotropic
