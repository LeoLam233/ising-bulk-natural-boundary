import IsingBulk.Preferred22.SelectedBranchDisk
import IsingBulk.Preferred22.PhysicalAnalytic

/-! Exact discriminant and logarithmic-derivative estimates for the actual
physical root. These apply to the selected true-branch parameter disks, with
constants independent of particle count. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 800000

lemma preferred_oneBody_discriminant {W : ℂ} (hW : OffRealSegment W) :
    (oneBody (physicalRoot W))^2=(W^2-1)⁻¹ := by
  let z := physicalRoot W
  have hz : z≠0 := physicalRoot_ne_zero W
  have hD : W^2-1≠0 := offRealSegment_discriminant_ne_zero hW
  have he : 1-z^2=2*z*(W-z) := by
    have h := physicalRoot_quadratic W
    dsimp only [z]
    linear_combination h
  have hdiff : W-z≠0 := by
    intro hh
    have hh' : physicalRoot W-W=0 := by
      dsimp only [z] at hh
      linear_combination -hh
    have h := physicalRoot_discriminant W
    rw [hh',zero_pow (by decide : 2≠0)] at h
    exact hD h.symm
  have ho : oneBody z=(W-z)⁻¹ := by
    unfold oneBody
    rw [he]
    field_simp
  rw [ho,inv_pow]
  congr 1
  have h := physicalRoot_discriminant W
  dsimp only [z]
  linear_combination h

lemma preferred_upper_discriminant_margin {W : ℂ} (_hW : 0≤W.im) :
    W.im≤‖W^2-1‖ := by
  have hminus : W.im≤‖W-1‖ := by
    simpa using Complex.im_le_norm (W-1)
  have hplus : W.im≤‖W+1‖ := by
    simpa using Complex.im_le_norm (W+1)
  have hsum : 2≤‖W-1‖+‖W+1‖ := by
    have h := norm_sub_le (W-1) (W+1)
    have he : (W-1)-(W+1)=(-2:ℂ) := by ring
    rw [he] at h
    norm_num at h
    exact h
  have he : W^2-1=(W-1)*(W+1) := by ring
  rw [he,norm_mul]
  by_cases hm : 1≤‖W-1‖
  · exact hplus.trans (le_mul_of_one_le_left (norm_nonneg _) hm)
  · have hp : 1≤‖W+1‖ := by linarith
    exact hminus.trans (le_mul_of_one_le_right (norm_nonneg _) hp)

/-- The genuine square-root branch loss, obtained from the exact quadratic
root equation rather than from a radial compactness envelope. -/
theorem preferred_physical_oneBody_upper_bound {W : ℂ} (hW : 0<W.im) :
    ‖oneBody (physicalRoot W)‖≤1/Real.sqrt W.im := by
  have hoff : OffRealSegment W := Or.inl (ne_of_gt hW)
  have hD : 0<‖W^2-1‖ := norm_pos_iff.mpr (offRealSegment_discriminant_ne_zero hoff)
  have he := congrArg (fun z : ℂ => ‖z‖) (preferred_oneBody_discriminant hoff)
  rw [norm_pow,norm_inv] at he
  have hb : ‖oneBody (physicalRoot W)‖^2≤1/W.im := by
    rw [he,inv_eq_one_div]
    exact one_div_le_one_div_of_le hW (preferred_upper_discriminant_margin hW.le)
  have hs : 0<Real.sqrt W.im := Real.sqrt_pos.mpr hW
  have hh : (1/Real.sqrt W.im)^2=1/W.im := by
    rw [div_pow,one_pow,Real.sq_sqrt hW.le]
  nlinarith [norm_nonneg (oneBody (physicalRoot W)),div_pos zero_lt_one hs]

/-- Exact physical-root derivative in the dispersion variable. -/
theorem preferred_physicalRoot_hasDerivAt {W : ℂ} (hW : OffRealSegment W) :
    HasDerivAt physicalRoot
      (-physicalRoot W*oneBody (physicalRoot W)) W := by
  have hf := (physicalRoot_analyticAt hW).differentiableAt.hasDerivAt
  have hz : physicalRoot W≠0 := physicalRoot_ne_zero W
  have ht := hf.add (hf.inv hz)
  have he : (fun V : ℂ => physicalRoot V+(physicalRoot V)⁻¹)=(fun V : ℂ => 2*V) :=
    funext physicalRoot_trace
  change HasDerivAt (fun V : ℂ => physicalRoot V+(physicalRoot V)⁻¹)
    (deriv physicalRoot W + -deriv physicalRoot W/(physicalRoot W)^2) W at ht
  rw [he] at ht
  have hh := ht.unique ((hasDerivAt_id W).const_mul 2)
  have hn : 1-(physicalRoot W)^2≠0 := by
    intro h
    have hh' : (physicalRoot W)^2=1 := by linear_combination -h
    have hn := physicalRoot_inside hW
    have hn' := congrArg (fun z : ℂ => ‖z‖) hh'
    rw [norm_pow,norm_one] at hn'
    nlinarith [norm_nonneg (physicalRoot W)]
  have hd : deriv physicalRoot W= -physicalRoot W*oneBody (physicalRoot W) := by
    unfold oneBody
    field_simp at hh ⊢
    linear_combination -hh
  rw [←hd]
  exact hf

/-- For a fixed deformed angle, the exact logarithmic derivative in the
complex temperature variable has the manuscript's square-root branch loss. -/
theorem preferred_selected_root_log_derivative {s w : ℂ}
    (hs : (1:ℝ)/2≤‖s‖) (hW : 0<(temperatureTrace s-Complex.cos w).im) :
    ‖deriv (fun t : ℂ => physicalRoot (temperatureTrace t-Complex.cos w)) s /
      physicalRoot (temperatureTrace s-Complex.cos w)‖≤
      5/Real.sqrt (temperatureTrace s-Complex.cos w).im := by
  have hs0 : s≠0 := by intro h; norm_num [h] at hs
  let W := temperatureTrace s-Complex.cos w
  have hw : OffRealSegment W := Or.inl (ne_of_gt hW)
  have hg : HasDerivAt (fun t : ℂ => temperatureTrace t-Complex.cos w)
      (1-1/s^2) s := by
    simpa [temperatureTrace,sub_eq_add_neg,neg_div] using
      (((hasDerivAt_id s).add ((hasDerivAt_id s).inv hs0)).sub_const (Complex.cos w))
  have hf := (preferred_physicalRoot_hasDerivAt hw).comp s hg
  change HasDerivAt (fun t : ℂ => physicalRoot (temperatureTrace t-Complex.cos w))
    (-physicalRoot W*oneBody (physicalRoot W)*(1-1/s^2)) s at hf
  have he : deriv (fun t : ℂ => physicalRoot (temperatureTrace t-Complex.cos w)) s /
      physicalRoot W= -oneBody (physicalRoot W)*(1-1/s^2) := by
    rw [hf.deriv]
    field_simp [physicalRoot_ne_zero W]
  rw [he,norm_mul,norm_neg]
  have hcoef : ‖(1:ℂ)-1/s^2‖≤5 := by
    have h := norm_sub_le (1:ℂ) (1/s^2)
    rw [norm_one,norm_div,norm_one,norm_pow] at h
    have hn : 0<‖s‖ := norm_pos_iff.mpr hs0
    have hi : (1:ℝ)/‖s‖^2≤4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
      nlinarith
    linarith
  have hbody := preferred_physical_oneBody_upper_bound hW
  calc
    _ ≤ (1/Real.sqrt W.im)*5 := mul_le_mul hbody hcoef (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end IsingBulk.Preferred22
