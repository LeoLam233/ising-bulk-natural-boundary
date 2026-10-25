import IsingBulk.Joint.Geometry.Modulus
import IsingBulk.Anisotropic.Geometry.CollinearSigns
import IsingBulk.Anisotropic.Geometry.CollinearRectangle

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

private theorem real_angle_rectangle (h c H C t V a b : ℝ)
    (hh : 0<h) (hH : 0<H) (hcpos : 0<c) (hCpos : 0<C)
    (hc : c^2-h^2=1) (hC : C^2-H^2=1) (ht : t^2=1) (hV : V^2=1)
    (ha : |a|≤1) (hb : |b|≤1) (he : c*C*t*V=h*t*a+H*V*b) :
    C^2*t^2-c^2*H^2=0 ∧ c^2*V^2-h^2*C^2=0 := by
  have hat : |t|=1 := by nlinarith [sq_abs t, abs_nonneg t]
  have haV : |V|=1 := by nlinarith [sq_abs V, abs_nonneg V]
  have hbound : c*C ≤ h+H := by
    calc
      c*C = |c*C*t*V| := by rw [abs_mul,abs_mul,abs_mul,abs_of_pos hcpos,abs_of_pos hCpos,hat,haV]; ring
      _ = |h*t*a+H*V*b| := congrArg abs he
      _ ≤ |h*t*a|+|H*V*b| := abs_add_le _ _
      _ = h*|a|+H*|b| := by rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_pos hh,abs_of_pos hH,hat,haV]; ring
      _ ≤ h+H := by nlinarith [mul_le_mul_of_nonneg_left ha hh.le, mul_le_mul_of_nonneg_left hb hH.le]
  have hi : (c*C)^2-(h+H)^2=(h*H-1)^2 := by
    linear_combination C^2*hc+(h^2+1)*hC
  have hs := mul_self_le_mul_self (mul_pos hcpos hCpos).le hbound
  have hz : (h*H-1)^2=0 := by nlinarith [sq_nonneg (h*H-1)]
  have hp : h*H=1 := by linarith [sq_eq_zero_iff.mp hz]
  rw [ht,hV]
  constructor
  · linear_combination hC-H^2*hc-(h*H+1)*hp
  · linear_combination hc-h^2*hC-(h*H+1)*hp

theorem signs_zero_of_mem_real_angles {K : Coupling}
    (hx : 0<K.1.re) (hu : 0<K.2.re)
    (hq : Real.sin K.1.im=0) (hQ : Real.sin K.2.im=0)
    (hK : K∈spectralSet) : F1 K=0 ∧ F2 K=0 := by
  rcases hK with ⟨a,ha,b,hb,he⟩
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, A_re, S_re, T_re, hq, hQ] at hre
  exact real_angle_rectangle _ _ _ _ _ _ a b
    (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr hu)
    (Real.cosh_pos _) (Real.cosh_pos _) (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _)
    (by simpa [hq] using Real.sin_sq_add_cos_sq K.1.im)
    (by simpa [hQ] using Real.sin_sq_add_cos_sq K.2.im)
    (abs_le.mpr ha) (abs_le.mpr hb) hre

theorem signs_of_mem_positive_quadrant {K : Coupling}
    (hx : 0<K.1.re) (hu : 0<K.2.re) (hK : K∈spectralSet) : F1 K*F2 K≤0 := by
  by_cases hq : Real.sin K.1.im ≠ 0 ∨ Real.sin K.2.im ≠ 0
  · exact (spectral_numerator_bounds_iff_signs hx hu hq).mp (spectral_numerator_bounds_of_mem hK)
  · push Not at hq
    rw [(signs_zero_of_mem_real_angles hx hu hq.1 hq.2 hK).1, zero_mul]

theorem norm_p_eq_one_of_zero_edges {K : Coupling} (hf : F1 K=0) (hg : F2 K=0) : ‖p K‖=1 := by
  have hs : ‖S K‖^2=Real.sinh K.1.re^2+Real.sin K.1.im^2 := norm_sinh_sq K.1
  have ht : ‖T K‖^2=Real.sinh K.2.re^2+Real.sin K.2.im^2 := norm_sinh_sq K.2
  have hp := edge_intersection_norm_product (Real.sinh K.1.re) (Real.cosh K.1.re)
    (Real.sinh K.2.re) (Real.cosh K.2.re) (Real.cos K.1.im) (Real.sin K.1.im)
    (Real.cos K.2.im) (Real.sin K.2.im) (Real.cosh_pos _)
    (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _) (Real.sin_sq_add_cos_sq _)
    (Real.sin_sq_add_cos_sq _) hf hg
  rw [← hs,← ht] at hp
  rw [p,norm_mul]
  have hn := mul_nonneg (norm_nonneg (S K)) (norm_nonneg (T K))
  nlinarith [sq_nonneg (‖S K‖*‖T K‖-1)]

theorem mem_spectralSet_of_collinear_zero_edges {K : Coupling}
    (hx : 0<K.1.re) (hu : 0<K.2.re) (hd : spectralDet K=0)
    (hf : F1 K=0) (hg : F2 K=0) : K∈spectralSet := by
  have hnV := spectralNV_sq_sub_det_sq K
  rw [hd,hf] at hnV
  have hnV0 : spectralNV K=0 := by
    apply sq_eq_zero_iff.mp
    simpa using hnV
  have hre : (S K).re ≠ 0 := by
    rw [S_re]
    apply mul_ne_zero (Real.sinh_pos_iff.mpr hx).ne'
    intro hcos
    have hprod := mul_pos (sq_pos_of_pos (Real.cosh_pos K.1.re))
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr hu))
    simp only [F1,hcos,zero_pow (by decide : 2≠0),mul_zero,zero_sub] at hf
    linarith
  exact collinear_rectangle_representation _ _ _ hre hd hnV0
    (dispersion_norm_bound _ _ _ (A_sq K) (norm_p_eq_one_of_zero_edges hf hg))

theorem mem_spectralSet_iff_signs_positive_quadrant {K : Coupling}
    (hx : 0<K.1.re) (hu : 0<K.2.re) : K∈spectralSet ↔ F1 K*F2 K≤0 := by
  constructor
  · exact signs_of_mem_positive_quadrant hx hu
  · intro hf
    by_cases hd : spectralDet K ≠ 0
    · exact (mem_spectralSet_iff_signs_of_det_ne_zero hx hu hd).mpr hf
    · push Not at hd
      by_cases hq : Real.sin K.1.im ≠ 0 ∨ Real.sin K.2.im ≠ 0
      · have hb := (spectral_numerator_bounds_iff_signs hx hu hq).mpr hf
        rw [spectralNU_formula,spectralNV_formula,spectralDet_formula] at hb
        have hd' := hd
        rw [spectralDet_formula] at hd'
        have he := zero_edges_of_collinear _ _ _ _ _ _ _ _
          (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr hu)
          (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _)
          (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _) hq hd' hb.1 hb.2
        exact mem_spectralSet_of_collinear_zero_edges hx hu hd he.1 he.2
      · push Not at hq
        have ht : Real.cos K.1.im^2=1 := by simpa [hq.1] using Real.sin_sq_add_cos_sq K.1.im
        have hT : Real.cos K.2.im^2=1 := by simpa [hq.2] using Real.sin_sq_add_cos_sq K.2.im
        have he : F1 K=F2 K := by
          unfold F1 F2
          rw [ht,hT]
          linear_combination -Real.cosh K.2.re^2*Real.cosh_sq_sub_sinh_sq K.1.re+
            Real.cosh K.1.re^2*Real.cosh_sq_sub_sinh_sq K.2.re
        have hz : F1 K=0 := by
          rw [← he] at hf
          nlinarith [sq_nonneg (F1 K)]
        exact mem_spectralSet_of_collinear_zero_edges hx hu hd hz (he ▸ hz)

end
end IsingBulk.Joint
