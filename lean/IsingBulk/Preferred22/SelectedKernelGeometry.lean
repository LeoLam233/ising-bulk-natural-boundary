import IsingBulk.Preferred22.RootMovement
import IsingBulk.Preferred22.SelectedRegularGap

/-! Algebraic pair-denominator geometry on the literal physical sheet.
The Cayley transform keeps both roots in one quadrant. This supplies a
uniform comparison with their distances from the branch root, without
assuming a pairwise denominator estimate or choosing continued phases. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma preferred_quadrant_norm_add {a b : ℂ}
    (ha : 0≤a.re ∧ 0≤a.im) (hb : 0≤b.re ∧ 0≤b.im) :
    ‖a‖+‖b‖≤2*‖a+b‖ := by
  have hna := Complex.norm_le_abs_re_add_abs_im a
  have hnb := Complex.norm_le_abs_re_add_abs_im b
  rw [abs_of_nonneg ha.1,abs_of_nonneg ha.2] at hna
  rw [abs_of_nonneg hb.1,abs_of_nonneg hb.2] at hnb
  have hr := Complex.re_le_norm (a+b)
  have hi := Complex.im_le_norm (a+b)
  simp only [Complex.add_re,Complex.add_im] at hr hi
  linarith

lemma preferred_cayley_quadrant {z : ℂ} (hz : ‖z‖≤1) (him : z.im≤0) :
    0≤((1-z)/(1+z)).re ∧ 0≤((1-z)/(1+z)).im := by
  have hsq : z.re^2+z.im^2≤1 := by
    have hn := Complex.normSq_eq_norm_sq z
    simp only [Complex.normSq_apply] at hn
    nlinarith [norm_nonneg z]
  constructor
  · rw [Complex.div_re,←add_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re,Complex.one_re,Complex.add_re,
      Complex.sub_im,Complex.one_im,Complex.add_im]
    nlinarith
  · rw [Complex.div_im,←sub_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re,Complex.one_re,Complex.add_re,
      Complex.sub_im,Complex.one_im,Complex.add_im]
    nlinarith

/-- The physical lower half disk has no cancellation between two branch
distances once the opposite endpoint `-1` is separated. -/
theorem preferred_pair_denominator_branch_lower {z v : ℂ} {η : ℝ}
    (hη : 0<η) (hz : ‖z‖≤1) (hv : ‖v‖≤1)
    (hzi : z.im≤0) (hvi : v.im≤0)
    (hzη : η≤‖1+z‖) (hvη : η≤‖1+v‖) :
    η^2/8*(‖1-z‖+‖1-v‖)≤‖1-z*v‖ := by
  have hzn : 1+z≠0 := norm_pos_iff.mp (hη.trans_le hzη)
  have hvn : 1+v≠0 := norm_pos_iff.mp (hη.trans_le hvη)
  let a := (1-z)/(1+z)
  let b := (1-v)/(1+v)
  have hquad := preferred_quadrant_norm_add (preferred_cayley_quadrant hz hzi)
    (preferred_cayley_quadrant hv hvi)
  change ‖a‖+‖b‖≤2*‖a+b‖ at hquad
  have ha : 1-z=a*(1+z) := by dsimp only [a]; field_simp
  have hb : 1-v=b*(1+v) := by dsimp only [b]; field_simp
  have hsum : ‖1-z‖+‖1-v‖≤2*(‖a‖+‖b‖) := by
    rw [ha,hb,norm_mul,norm_mul]
    have h₁ : ‖1+z‖≤2 := (norm_add_le _ _).trans (by simpa only [norm_one] using (by linarith : (1:ℝ)+‖z‖≤2))
    have h₂ : ‖1+v‖≤2 := (norm_add_le _ _).trans (by simpa only [norm_one] using (by linarith : (1:ℝ)+‖v‖≤2))
    nlinarith [norm_nonneg a,norm_nonneg b]
  have he : (1+z)*(1+v)*(a+b)=2*(1-z*v) := by
    dsimp only [a,b]
    field_simp
    ring
  have hn := congrArg (fun w : ℂ => ‖w‖) he
  simp only [norm_mul,Complex.norm_ofNat] at hn
  have hp : η^2≤‖1+z‖*‖1+v‖ := by
    nlinarith [mul_le_mul hzη hvη hη.le (norm_nonneg (1+z))]
  have hmul := mul_le_mul_of_nonneg_right hp (norm_nonneg (a+b))
  nlinarith [sq_nonneg η]

lemma preferred_physical_root_im_neg {W : ℂ} (hW : 0<W.im) :
    (physicalRoot W).im<0 := by
  have hoff : OffRealSegment W := Or.inl hW.ne'
  have hz := physicalRoot_inside hoff
  have hz0 := norm_pos_iff.mpr (physicalRoot_ne_zero W)
  have ht := congrArg Complex.im (physicalRoot_trace W)
  simp only [Complex.add_im,Complex.inv_im,Complex.normSq_eq_norm_sq,
    Complex.mul_im] at ht
  norm_num at ht
  rw [neg_div] at ht
  have hsq : 0<‖physicalRoot W‖^2 := sq_pos_of_pos hz0
  have he : (physicalRoot W).im*(‖physicalRoot W‖^2-1)=
      2*W.im*‖physicalRoot W‖^2 := by
    have hh := (eq_div_iff hsq.ne').mp
      (show (physicalRoot W).im-2*W.im=(physicalRoot W).im/‖physicalRoot W‖^2 by linarith)
    nlinarith
  have hneg : ‖physicalRoot W‖^2-1<0 := by nlinarith
  nlinarith [mul_pos hW hsq]

lemma preferred_physical_root_branch_squares (W : ℂ) :
    (1-physicalRoot W)^2=2*physicalRoot W*(W-1) ∧
      (1+physicalRoot W)^2=2*physicalRoot W*(W+1) := by
  constructor <;> linear_combination physicalRoot_quadratic W

lemma preferred_physical_root_lower {W : ℂ} {R : ℝ}
    (hW : OffRealSegment W) (hR : ‖W‖≤R) :
    1/(2*R+1)≤‖physicalRoot W‖ := by
  have hK : 0<2*R+1 := by linarith [norm_nonneg W]
  have hz : 0<‖physicalRoot W‖ := norm_pos_iff.mpr (physicalRoot_ne_zero W)
  have hi := preferred_physical_root_inverse_bound hW hR
  rw [norm_inv,←one_div] at hi
  apply (div_le_iff₀ hK).mpr
  have hh := (div_le_iff₀ hz).mp hi
  nlinarith

/-- A dispersion margin at the opposite branch endpoint gives the exact
uniform separation required by the lower-half-disk pair lemma. -/
lemma preferred_physical_root_plus_lower {W : ℂ} {R H η : ℝ}
    (hW : OffRealSegment W) (hR : ‖W‖≤R) (hH : 0≤H)
    (hWH : H≤‖W+1‖) (_hη : 0≤η) (hηsq : η^2≤2*H/(2*R+1)) :
    η≤‖1+physicalRoot W‖ := by
  have hroot := preferred_physical_root_lower hW hR
  have he := congrArg (fun x : ℂ => ‖x‖) (preferred_physical_root_branch_squares W).2
  simp only [norm_pow,norm_mul,Complex.norm_ofNat] at he
  have hm := mul_le_mul hroot hWH hH (norm_nonneg _)
  have hh : η^2≤‖1+physicalRoot W‖^2 := by
    calc
      _ ≤ 2*H/(2*R+1) := hηsq
      _ = 2*((1/(2*R+1))*H) := by ring
      _ ≤ 2*(‖physicalRoot W‖*‖W+1‖) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by nlinarith [he]
  nlinarith [norm_nonneg (1+physicalRoot W)]

/-- A squared denominator bound retains the sum of both genuine branch
distances. In particular, opposite-plateau occupancy contributions add. -/
theorem preferred_physical_pair_squared_lower {W V : ℂ} {η μ : ℝ}
    (hW : 0<W.im) (hV : 0<V.im) (hη : 0<η) (_hμ : 0≤μ)
    (hzη : η≤‖1+physicalRoot W‖) (hvη : η≤‖1+physicalRoot V‖)
    (hzμ : μ≤‖physicalRoot W‖) (hvμ : μ≤‖physicalRoot V‖) :
    2*(η^2/8)^2*μ*(‖W-1‖+‖V-1‖)≤
      ‖1-physicalRoot W*physicalRoot V‖^2 := by
  let a := ‖1-physicalRoot W‖
  let b := ‖1-physicalRoot V‖
  let c := η^2/8
  let D := ‖1-physicalRoot W*physicalRoot V‖
  have hc : 0≤c := by dsimp only [c]; positivity
  have hp := preferred_pair_denominator_branch_lower hη
    (physicalRoot_inside (Or.inl hW.ne')).le (physicalRoot_inside (Or.inl hV.ne')).le
    (preferred_physical_root_im_neg hW).le (preferred_physical_root_im_neg hV).le hzη hvη
  change c*(a+b)≤D at hp
  have ha : 0≤a := norm_nonneg _
  have hb : 0≤b := norm_nonneg _
  have hD : 0≤D := norm_nonneg _
  have hs : c^2*(a^2+b^2)≤D^2 := by
    have hs := sq_le_sq₀ (mul_nonneg hc (add_nonneg ha hb)) hD |>.mpr hp
    nlinarith [mul_nonneg (sq_nonneg c) (mul_nonneg ha hb)]
  have heW := congrArg (fun x : ℂ => ‖x‖) (preferred_physical_root_branch_squares W).1
  have heV := congrArg (fun x : ℂ => ‖x‖) (preferred_physical_root_branch_squares V).1
  simp only [norm_pow,norm_mul,Complex.norm_ofNat] at heW heV
  have hwa := mul_le_mul_of_nonneg_right hzμ (norm_nonneg (W-1))
  have hvb := mul_le_mul_of_nonneg_right hvμ (norm_nonneg (V-1))
  have hsum : 2*μ*(‖W-1‖+‖V-1‖)≤a^2+b^2 := by
    dsimp only [a,b]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg c)
  change 2*c^2*μ*(‖W-1‖+‖V-1‖)≤D^2
  nlinarith

/-- Same-branch cancellation on the dispersion curve, in a form that is
valid for the explicit root continuation as well as the physical center. -/
theorem preferred_pair_reciprocal_identity {y u z v S : ℂ}
    (hy : y≠0) (hu : u≠0) (hz : z≠0) (hv : v≠0)
    (h₁ : y+y⁻¹+z+z⁻¹=2*S) (h₂ : u+u⁻¹+v+v⁻¹=2*S)
    (hD : 1-z*v≠0) (hY : 1-y*u≠0) :
    (y-u)/(1-z*v)=-(z-v)*y*u/((1-y*u)*z*v) := by
  have ht := h₁.trans h₂.symm
  field_simp at ht ⊢
  linear_combination -ht

end
end IsingBulk.Preferred22
