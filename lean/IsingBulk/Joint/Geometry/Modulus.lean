import IsingBulk.Joint.Geometry.Coordinates
import IsingBulk.Anisotropic.Geometry.Isotropic

namespace IsingBulk.Joint
noncomputable section

private theorem product_lt_one_of_scaled {a b r s : ℝ}
    (ha : 0<a) (hb : 0<b) (hr : 0≤r) (hs : 0≤s)
    (h1 : b*r<a) (h2 : a*s<b) : r*s<1 := by
  have h3 := mul_lt_mul_of_pos_left h2 ha
  have h4 := mul_le_mul_of_nonneg_right h1.le (mul_nonneg ha.le hs)
  have hab := mul_pos ha hb
  nlinarith

private theorem one_lt_product_of_scaled {a b r s : ℝ}
    (ha : 0<a) (hb : 0<b) (hr : 0≤r) (_hs : 0≤s)
    (h1 : a<b*r) (h2 : b<a*s) : 1<r*s := by
  have h3 := mul_lt_mul_of_pos_left h2 ha
  have h4 := mul_lt_mul_of_pos_right h1 (lt_trans hb h2)
  have hab := mul_pos ha hb
  nlinarith

/-- The exact modulus identity underlying JOINT (2.13). -/
theorem norm_S_sq (K : Coupling) : ‖S K‖^2 = Real.cosh K.1.re^2 - Real.cos K.1.im^2 := by
  have h := IsingBulk.Anisotropic.norm_sinh_sq K.1
  change ‖S K‖^2 = _ at h
  nlinarith [Real.cosh_sq_sub_sinh_sq K.1.re, Real.sin_sq_add_cos_sq K.1.im]

theorem norm_T_sq (K : Coupling) : ‖T K‖^2 = Real.cosh K.2.re^2 - Real.cos K.2.im^2 := by
  have h := IsingBulk.Anisotropic.norm_sinh_sq K.2
  change ‖T K‖^2 = _ at h
  nlinarith [Real.cosh_sq_sub_sinh_sq K.2.re, Real.sin_sq_add_cos_sq K.2.im]

theorem norm_p_sq (K : Coupling) : ‖p K‖^2 =
    (Real.cosh K.1.re^2 - Real.cos K.1.im^2) *
    (Real.cosh K.2.re^2 - Real.cos K.2.im^2) := by
  rw [p, norm_mul, mul_pow, norm_S_sq, norm_T_sq]

/-- Equal edge signs determine the product side, with no fixed-ratio assumption. -/
theorem norm_p_lt_one_of_positive_signs {K : Coupling} (h1 : 0<F1 K) (h2 : 0<F2 K) :
    ‖p K‖<1 := by
  have he1 := Real.cosh_sq_sub_sinh_sq K.1.re
  have he2 := Real.cosh_sq_sub_sinh_sq K.2.re
  have hr : 0≤Real.cosh K.1.re^2-Real.cos K.1.im^2 := by rw [← norm_S_sq]; positivity
  have hs : 0≤Real.cosh K.2.re^2-Real.cos K.2.im^2 := by rw [← norm_T_sq]; positivity
  have h := product_lt_one_of_scaled
    (sq_pos_of_pos (Real.cosh_pos K.1.re)) (sq_pos_of_pos (Real.cosh_pos K.2.re)) hr hs
    (by dsimp [F1] at h1; nlinarith [he2])
    (by dsimp [F2] at h2; nlinarith [he1])
  rw [← norm_p_sq] at h
  nlinarith [norm_nonneg (p K)]

theorem one_lt_norm_p_of_negative_signs {K : Coupling} (h1 : F1 K<0) (h2 : F2 K<0) :
    1<‖p K‖ := by
  have he1 := Real.cosh_sq_sub_sinh_sq K.1.re
  have he2 := Real.cosh_sq_sub_sinh_sq K.2.re
  have hr : 0≤Real.cosh K.1.re^2-Real.cos K.1.im^2 := by rw [← norm_S_sq]; positivity
  have hs : 0≤Real.cosh K.2.re^2-Real.cos K.2.im^2 := by rw [← norm_T_sq]; positivity
  have h := one_lt_product_of_scaled
    (sq_pos_of_pos (Real.cosh_pos K.1.re)) (sq_pos_of_pos (Real.cosh_pos K.2.re)) hr hs
    (by dsimp [F1] at h1; nlinarith [he2])
    (by dsimp [F2] at h2; nlinarith [he1])
  rw [← norm_p_sq] at h
  nlinarith [norm_nonneg (p K)]

private theorem cosh_abs (x : ℝ) : Real.cosh |x| = Real.cosh x := by
  rcases le_or_gt 0 x with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Real.cosh_neg]

private theorem sinh_abs_sq (x : ℝ) : Real.sinh |x| ^ 2 = Real.sinh x ^ 2 := by
  rcases le_or_gt 0 x with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Real.sinh_neg, neg_sq]

theorem positive_edge_of_high {x u y : ℝ}
    (hy : |y|<Real.pi/2) (h : Real.cosh x*Real.tanh |u|<Real.cos y) :
    0<Real.cosh u^2*Real.cos y^2-Real.cosh x^2*Real.sinh u^2 := by
  have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp hy)
  have hu := Real.cosh_pos u
  have hs : 0≤Real.sinh |u| := Real.sinh_nonneg_iff.mpr (abs_nonneg u)
  rw [Real.tanh_eq_sinh_div_cosh, cosh_abs, ← mul_div_assoc, div_lt_iff₀ hu] at h
  have hn : 0≤Real.cosh x*Real.sinh |u| := mul_nonneg (Real.cosh_pos x).le hs
  have he : (Real.cosh x*Real.sinh |u|)^2 < (Real.cos y*Real.cosh u)^2 := by nlinarith
  rw [mul_pow,mul_pow,sinh_abs_sq] at he
  nlinarith

theorem negative_edge_of_low {x u y : ℝ}
    (h : |Real.cos y|<Real.cosh x*Real.tanh u) :
    Real.cosh u^2*Real.cos y^2-Real.cosh x^2*Real.sinh u^2<0 := by
  have hu := Real.cosh_pos u
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc, lt_div_iff₀ hu] at h
  have hn : 0≤|Real.cos y| *Real.cosh u := mul_nonneg (abs_nonneg _) hu.le
  have he : (|Real.cos y| *Real.cosh u)^2 < (Real.cosh x*Real.sinh u)^2 := by nlinarith
  rw [mul_pow,mul_pow,sq_abs] at he
  nlinarith

theorem positive_signs_of_mem_highDomain {K : Coupling} (hK : K∈highDomain) :
    0<F1 K ∧ 0<F2 K := by
  exact ⟨positive_edge_of_high hK.1 hK.2.2.1,
    by simpa [F2,mul_comm] using positive_edge_of_high hK.2.1 hK.2.2.2⟩

theorem negative_signs_of_mem_lowDomain {K : Coupling} (hK : K∈lowDomain) :
    F1 K<0 ∧ F2 K<0 := by
  exact ⟨negative_edge_of_low hK.2.2.1,
    by simpa [F2,mul_comm] using negative_edge_of_low hK.2.2.2⟩

theorem norm_p_lt_one {K : Coupling} (hK : K∈highDomain) : ‖p K‖<1 :=
  norm_p_lt_one_of_positive_signs (positive_signs_of_mem_highDomain hK).1
    (positive_signs_of_mem_highDomain hK).2

theorem one_lt_norm_p {K : Coupling} (hK : K∈lowDomain) : 1<‖p K‖ :=
  one_lt_norm_p_of_negative_signs (negative_signs_of_mem_lowDomain hK).1
    (negative_signs_of_mem_lowDomain hK).2

end
end IsingBulk.Joint
