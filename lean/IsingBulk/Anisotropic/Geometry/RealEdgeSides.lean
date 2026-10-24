import IsingBulk.Anisotropic.Geometry.RegularEdges

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

theorem spectralS_ne_zero_of_det_ne_zero {lam : ℝ} {z : ℂ} (hd : spectralDet lam z≠0) : spectralS z≠0 := by
  intro h
  apply hd
  simp [spectralDet,h]

theorem spectralT_ne_zero_of_det_ne_zero {lam : ℝ} {z : ℂ} (hd : spectralDet lam z≠0) : spectralT lam z≠0 := by
  intro h
  apply hd
  simp [spectralDet,h]

theorem edgeMapU_analyticAt {lam : ℝ} {e z : ℂ} (ht : spectralT lam z≠0) :
    AnalyticAt ℂ (edgeMapU lam e) z := by
  apply AnalyticAt.div _ _ ht
  · unfold spectralA spectralS
    fun_prop
  · unfold spectralT
    fun_prop

theorem edgeMapV_analyticAt {lam : ℝ} {e z : ℂ} (hs : spectralS z≠0) :
    AnalyticAt ℂ (edgeMapV lam e) z := by
  apply AnalyticAt.div _ _ hs
  · unfold spectralA spectralT
    fun_prop
  · unfold spectralS
    fun_prop

theorem edgeMapU_im_identity {lam : ℝ} {z : ℂ} (hd : spectralDet lam z≠0) (e : ℝ) :
    (edgeMapU lam (e:ℂ) z).im*Complex.normSq (spectralT lam z)=spectralDet lam z*(e-spectralU lam z) := by
  have ht := spectralT_ne_zero_of_det_ne_zero hd
  have htn : Complex.normSq (spectralT lam z)≠0 := (Complex.normSq_pos.mpr ht).ne'
  unfold edgeMapU
  rw [Complex.div_im,←sub_div,div_mul_cancel₀ _ htn]
  simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  unfold spectralU
  rw [mul_sub,mul_div_cancel₀ _ hd]
  unfold spectralDet spectralNU
  ring

theorem edgeMapV_im_identity {lam : ℝ} {z : ℂ} (hd : spectralDet lam z≠0) (e : ℝ) :
    (edgeMapV lam (e:ℂ) z).im*Complex.normSq (spectralS z)= -spectralDet lam z*(e-spectralV lam z) := by
  have hs := spectralS_ne_zero_of_det_ne_zero hd
  have hsn : Complex.normSq (spectralS z)≠0 := (Complex.normSq_pos.mpr hs).ne'
  unfold edgeMapV
  rw [Complex.div_im,←sub_div,div_mul_cancel₀ _ hsn]
  simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  unfold spectralV
  rw [neg_mul,mul_sub,mul_div_cancel₀ _ hd]
  unfold spectralDet spectralNV
  ring

theorem endpoint_halfplane_iff (u v d t h e c : ℝ) (he : e=1 ∨ e= -1)
    (ht : 0<t) (hc : c*d*e<0) (hu : |u-e|<1) (hv : |v|<1)
    (hr : h*t=d*(e-u)) :
    (|u|≤1 ∧ |v|≤1) ↔ c*h≤0 := by
  have he2 : e^2=1 := by rcases he with rfl | rfl <;> norm_num
  have hrel : (c*h)*t=(c*d*e)*(1-e*u) := by
    linear_combination c*hr+c*d*u*he2
  have hs : c*h≤0 ↔ e*u≤1 := by
    constructor
    · intro hh
      by_contra hn
      have hp := mul_pos_of_neg_of_neg hc (sub_neg.mpr (lt_of_not_ge hn))
      have hnp := mul_nonpos_of_nonpos_of_nonneg hh ht.le
      linarith
    · intro hu'
      by_contra hn
      have hp := mul_pos (lt_of_not_ge hn) ht
      have hnp := mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.mpr hu')
      linarith
  rw [hs]
  have hub := abs_lt.mp hu
  have hvb := hv.le
  rcases he with rfl | rfl
  · simp only [one_mul]
    rw [abs_le]
    constructor
    · exact fun h => h.1.2
    · intro h
      exact ⟨⟨by linarith,h⟩,hvb⟩
  · simp only [neg_mul,one_mul]
    rw [abs_le]
    constructor
    · intro h
      linarith [h.1.1]
    · intro h
      exact ⟨⟨by linarith,by linarith⟩,hvb⟩


/-- A rescaled actual U-endpoint coordinate defines the spectral set locally as one closed half-plane. -/
theorem actual_U_edge_halfplane {lam : ℝ} {z : ℂ} {e : ℝ}
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hu : spectralU lam z=e)
    (hv : |spectralV lam z|<1) :
    ∀ᶠ w in 𝓝 z, w∈spectralSet lam ↔
      (((-e*spectralDet lam z:ℝ):ℂ)*edgeMapU lam (e:ℂ) w).im≤0 := by
  have he2 : e^2=1 := by rcases he with rfl | rfl <;> norm_num
  have hD : ∀ᶠ w in 𝓝 z, 0<spectralDet lam z*spectralDet lam w :=
    (continuous_const.mul (spectralDet_continuous lam)).continuousAt.eventually_const_lt
      (by change 0<spectralDet lam z*spectralDet lam z; nlinarith [sq_pos_of_ne_zero hd])
  have hU : ∀ᶠ w in 𝓝 z, |spectralU lam w-e|<1 :=
    ((spectralU_continuousAt hd).sub_const e).abs.eventually_lt_const (by simp [hu])
  have hV : ∀ᶠ w in 𝓝 z, |spectralV lam w|<1 :=
    (spectralV_continuousAt hd).abs.eventually_lt_const hv
  filter_upwards [hD,hU,hV] with w hwd hwu hwv
  have hdw : spectralDet lam w≠0 := by intro h; simp [h] at hwd
  rw [mem_spectralSet_iff_coordinates hdw]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  apply endpoint_halfplane_iff _ _ _ _ _ _ _ he
    (Complex.normSq_pos.mpr (spectralT_ne_zero_of_det_ne_zero hdw)) _ hwu hwv
    (edgeMapU_im_identity hdw e)
  have hi : (-e*spectralDet lam z)*spectralDet lam w*e= -(spectralDet lam z*spectralDet lam w) := by
    linear_combination -spectralDet lam z*spectralDet lam w*he2
  rw [hi]
  linarith

/-- The axis-swapped endpoint has the corresponding, oppositely oriented half-plane chart. -/
theorem actual_V_edge_halfplane {lam : ℝ} {z : ℂ} {e : ℝ}
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hv : spectralV lam z=e)
    (hu : |spectralU lam z|<1) :
    ∀ᶠ w in 𝓝 z, w∈spectralSet lam ↔
      (((e*spectralDet lam z:ℝ):ℂ)*edgeMapV lam (e:ℂ) w).im≤0 := by
  have he2 : e^2=1 := by rcases he with rfl | rfl <;> norm_num
  have hD : ∀ᶠ w in 𝓝 z, 0<spectralDet lam z*spectralDet lam w :=
    (continuous_const.mul (spectralDet_continuous lam)).continuousAt.eventually_const_lt
      (by change 0<spectralDet lam z*spectralDet lam z; nlinarith [sq_pos_of_ne_zero hd])
  have hV : ∀ᶠ w in 𝓝 z, |spectralV lam w-e|<1 :=
    ((spectralV_continuousAt hd).sub_const e).abs.eventually_lt_const (by simp [hv])
  have hU : ∀ᶠ w in 𝓝 z, |spectralU lam w|<1 :=
    (spectralU_continuousAt hd).abs.eventually_lt_const hu
  filter_upwards [hD,hU,hV] with w hwd hwu hwv
  have hdw : spectralDet lam w≠0 := by intro h; simp [h] at hwd
  rw [mem_spectralSet_iff_coordinates hdw,and_comm]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  apply endpoint_halfplane_iff _ _ _ _ _ _ _ he
    (Complex.normSq_pos.mpr (spectralS_ne_zero_of_det_ne_zero hdw)) _ hwv hwu
    (edgeMapV_im_identity hdw e)
  have hi : (e*spectralDet lam z)*(-spectralDet lam w)*e= -(spectralDet lam z*spectralDet lam w) := by
    linear_combination -spectralDet lam z*spectralDet lam w*he2
  rw [hi]
  linarith

end
end IsingBulk.Anisotropic
