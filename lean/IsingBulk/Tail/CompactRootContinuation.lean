import IsingBulk.First.GlobalResidueRoot

/-! Actual compact root continuations and a negative branch-cut regression.
The principal formula on Im W>0 is not itself an enlarged-disk continuation. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch ComplexOrder
open scoped Topology

def compactLeftRoot (W : ℂ) : ℂ := W-Complex.sqrt (W-1)*Complex.sqrt (W+1)

theorem compactLeftRoot_quadratic (W : ℂ) :
    compactLeftRoot W ^ 2 - 2*W*compactLeftRoot W + 1 = 0 := by
  have h₁ := sqrt_sq (W-1)
  have h₂ := sqrt_sq (W+1)
  dsimp [compactLeftRoot]
  calc
    _ = (Complex.sqrt (W-1))^2*(Complex.sqrt (W+1))^2-W^2+1 := by ring
    _ = 0 := by rw [h₁,h₂]; ring

theorem compactLeftRoot_nonzero (W : ℂ) : compactLeftRoot W ≠ 0 := by
  intro h
  have hh := compactLeftRoot_quadratic W
  rw [h] at hh
  norm_num at hh

theorem compactLeftRoot_analyticAt {W : ℂ} (hW : 1 < W.re) :
    AnalyticAt ℂ compactLeftRoot W := by
  apply DifferentiableOn.analyticAt (s := {W : ℂ | 1 < W.re})
  · intro z hz
    change 1 < z.re at hz
    have h₁ : z-1 ∈ Complex.slitPlane := Or.inl (by simp; linarith)
    have h₂ : z+1 ∈ Complex.slitPlane := Or.inl (by simp; linarith)
    exact (differentiableAt_id.sub
      (((Complex.differentiableAt_sqrt h₁).comp z (differentiableAt_id.sub_const 1)).mul
        ((Complex.differentiableAt_sqrt h₂).comp z (differentiableAt_id.add_const 1)))).differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hW

/-- The original expression is regular through the compact-right interval. -/
theorem interiorRoot_analyticAt_compactRight {W : ℂ} (hW : |W.re| < 1) :
    AnalyticAt ℂ interiorRoot W := by
  apply DifferentiableOn.analyticAt (s := {W : ℂ | |W.re| < 1})
  · intro z hz
    change |z.re| < 1 at hz
    have hs : 1-z^2 ∈ Complex.slitPlane := by
      left
      simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re]
      have hh := abs_lt.mp hz
      nlinarith [sq_nonneg z.im]
    have hp : DifferentiableAt ℂ (fun w : ℂ => 1-w^2) z := by fun_prop
    have hsqrt := (Complex.differentiableAt_sqrt hs).comp z hp
    have hroot : DifferentiableAt ℂ inverseCosineRoot z :=
      differentiableAt_id.add (hsqrt.const_mul Complex.I)
    exact (hroot.inv (inverseCosineRoot_ne_zero z)).differentiableWithinAt
  · exact (isOpen_lt (Complex.continuous_re.abs) continuous_const).mem_nhds hW

theorem sqrt_upper_orientation {D : ℂ} (him : 0 < D.im) :
    0 < (Complex.sqrt D).re ∧ 0 < (Complex.sqrt D).im := by
  have hn : D.re^2+D.im^2 = ‖D‖^2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq D)
  have hnorm := norm_nonneg D
  have him2 : 0 < D.im^2 := sq_pos_of_pos him
  have hre := Complex.abs_re_le_norm D
  have ha : 0 < ‖D‖+D.re := by
    have := (abs_le.mp hre).1
    nlinarith
  have hb : 0 < ‖D‖-D.re := by
    have := (abs_le.mp hre).2
    nlinarith
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [him.le, ite_true, one_mul, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add, mul_one]
  exact ⟨Real.sqrt_pos.mpr (by linarith),Real.sqrt_pos.mpr (by linarith)⟩

/-- Constructed agreement on the physical sheet, not an assumed glue field. -/
theorem compactLeftRoot_eq_interiorRoot {W : ℂ} (hre : 1 < W.re)
    (him : 0 < W.im) : compactLeftRoot W = interiorRoot W := by
  let d := Complex.sqrt (W-1)*Complex.sqrt (W+1)
  have hd2 : d^2 = W^2-1 := by
    dsimp [d]
    rw [mul_pow, sqrt_sq, sqrt_sq]
    ring
  have h₁ := sqrt_upper_orientation (show 0 < (W-1).im by simpa using him)
  have h₂ := sqrt_upper_orientation (show 0 < (W+1).im by simpa using him)
  have hdi : 0 < d.im := by
    dsimp [d]
    rw [Complex.mul_im]
    exact add_pos (mul_pos h₁.1 h₂.2) (mul_pos h₁.2 h₂.1)
  have hdr : 0 < d.re := by
    have hi := congrArg Complex.im hd2
    simp only [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im, sub_zero] at hi
    have hp : 0 < W.re*W.im := mul_pos (by linarith) him
    nlinarith
  have hout : 1 < ‖W+d‖ := by
    have hr := Complex.re_le_norm (W+d)
    rw [Complex.add_re] at hr
    linarith
  have hproduct : (W+d)*compactLeftRoot W = 1 := by
    change (W+d)*(W-d)=1
    linear_combination -hd2
  have heq : compactLeftRoot W = (W+d)⁻¹ := by
    have hn : W+d ≠ 0 := by intro h; rw [h, norm_zero] at hout; linarith
    apply (mul_left_cancel₀ hn)
    rw [hproduct, mul_inv_cancel₀ hn]
  have hz : ‖compactLeftRoot W‖ < 1 := by
    rw [heq, norm_inv]
    exact inv_lt_one_of_one_lt₀ hout
  have hw := interiorRoot_norm_lt_one him
  have hzq := compactLeftRoot_quadratic W
  have hwq := interiorRoot_quadratic W
  have hfactor : (compactLeftRoot W-interiorRoot W)*
      (compactLeftRoot W*interiorRoot W-1)=0 := by
    linear_combination interiorRoot W*hzq-compactLeftRoot W*hwq
  rcases mul_eq_zero.mp hfactor with he | he
  · exact sub_eq_zero.mp he
  · have hp := congrArg norm (sub_eq_zero.mp he)
    rw [norm_mul, norm_one] at hp
    have hnz := norm_nonneg (compactLeftRoot W)
    have hnw := norm_nonneg (interiorRoot W)
    nlinarith

theorem sqrt_right_halfplane {D : ℂ} (hD : 0 < D.re) :
    |(Complex.sqrt D).im| < (Complex.sqrt D).re := by
  have hs := congrArg Complex.re (sqrt_sq D)
  simp only [pow_two,Complex.mul_re] at hs
  have hn := sqrt_real_nonnegative D
  nlinarith [sq_abs (Complex.sqrt D).im, abs_nonneg (Complex.sqrt D).im]

/-- The compact-left continuation remains the interior root throughout its
entire half-plane, not just on the physical upper-half-plane overlap. -/
theorem compactLeftRoot_norm_lt_one {W : ℂ} (hW : 1 < W.re) :
    ‖compactLeftRoot W‖ < 1 := by
  let a := Complex.sqrt (W-1)
  let b := Complex.sqrt (W+1)
  have ha : |a.im| < a.re := sqrt_right_halfplane (by simp; linarith)
  have hb : |b.im| < b.re := sqrt_right_halfplane (by simp; linarith)
  have hbr : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hb
  have hab : |a.im| * |b.im| < a.re*b.re :=
    (mul_le_mul_of_nonneg_left hb.le (abs_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right ha hbr)
  have hd : 0 < (a*b).re := by
    rw [Complex.mul_re]
    have h := le_abs_self (a.im*b.im)
    rw [abs_mul] at h
    linarith
  have hout : 1 < ‖W+a*b‖ := by
    have h := Complex.re_le_norm (W+a*b)
    rw [Complex.add_re] at h
    linarith
  have hp : (W+a*b)*compactLeftRoot W=1 := by
    have ha2 : a^2=W-1 := sqrt_sq (W-1)
    have hb2 : b^2=W+1 := sqrt_sq (W+1)
    change (W+a*b)*(W-a*b)=1
    calc
      _ = W^2-a^2*b^2 := by ring
      _ = 1 := by rw [ha2,hb2]; ring
  have he : compactLeftRoot W=(W+a*b)⁻¹ := eq_inv_of_mul_eq_one_right hp
  rw [he,norm_inv]
  exact inv_lt_one_of_one_lt₀ hout

/-- Physical real compact-left root, including the strict interior bound. -/
theorem compactLeftRoot_real_formula {w : ℝ} (hw : 1 < w) :
    compactLeftRoot (w:ℂ) = ((w-Real.sqrt (w^2-1):ℝ):ℂ) := by
  have h₁ : (0:ℂ) ≤ (w:ℂ)-1 := by constructor <;> simp; linarith
  have h₂ : (0:ℂ) ≤ (w:ℂ)+1 := by constructor <;> simp; linarith
  unfold compactLeftRoot
  rw [Complex.sqrt_of_nonneg h₁, Complex.sqrt_of_nonneg h₂]
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.one_re]
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by linarith : 0 ≤ w-1)]
  have he : (w-1)*(w+1)=w^2-1 := by ring
  rw [he]
  push_cast
  rfl

theorem compactLeftRoot_real_bounds {w : ℝ} (hw : 1 < w) :
    0 < (compactLeftRoot (w:ℂ)).re ∧
      (compactLeftRoot (w:ℂ)).im = 0 ∧ ‖compactLeftRoot (w:ℂ)‖ < 1 := by
  have hsq : 0 ≤ w^2-1 := by nlinarith
  have hr := Real.sqrt_nonneg (w^2-1)
  have hr2 := Real.sq_sqrt hsq
  have hlo : 0 < w-Real.sqrt (w^2-1) := by nlinarith
  have hhi : w-Real.sqrt (w^2-1) < 1 := by nlinarith
  rw [compactLeftRoot_real_formula hw]
  refine ⟨hlo,rfl,?_⟩
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlo]
  exact hhi

/-- A single pointwise representative of the local continuation cover. The
excluded line below W=1 is deliberately not asserted to be regular. -/
def continuedRoot (W : ℂ) : ℂ :=
  if 1 < W.re then compactLeftRoot W else interiorRoot W

def continuedRootDomain : Set ℂ :=
  {W | 0 < W.im} ∪ {W | 1 < W.re} ∪ {W | |W.re| < 1}

theorem continuedRootDomain_isOpen : IsOpen continuedRootDomain :=
  ((isOpen_lt continuous_const Complex.continuous_im).union
    (isOpen_lt continuous_const Complex.continuous_re)).union
      (isOpen_lt Complex.continuous_re.abs continuous_const)

theorem continuedRoot_eq_interiorRoot {W : ℂ} (hW : 0 < W.im) :
    continuedRoot W = interiorRoot W := by
  unfold continuedRoot
  split_ifs with h
  · exact compactLeftRoot_eq_interiorRoot h hW
  · rfl

theorem continuedRoot_quadratic (W : ℂ) :
    continuedRoot W^2-2*W*continuedRoot W+1=0 := by
  unfold continuedRoot
  split_ifs
  · exact compactLeftRoot_quadratic W
  · exact interiorRoot_quadratic W

theorem continuedRoot_nonzero (W : ℂ) : continuedRoot W ≠ 0 := by
  unfold continuedRoot
  split_ifs
  · exact compactLeftRoot_nonzero W
  · exact interiorRoot_nonzero W

theorem continuedRoot_analyticAt {W : ℂ} (hW : W ∈ continuedRootDomain) :
    AnalyticAt ℂ continuedRoot W := by
  rcases hW with (hupper | hleft) | hright
  · have hneigh : ∀ᶠ z in 𝓝 W, 0 < z.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hupper
    have ha : AnalyticAt ℂ interiorRoot W := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [hneigh] with z hz
      exact interiorRoot_differentiableAt hz
    apply ha.congr
    filter_upwards [hneigh] with z hz
    exact (continuedRoot_eq_interiorRoot hz).symm
  · apply (compactLeftRoot_analyticAt hleft).congr
    have hneigh : ∀ᶠ z in 𝓝 W, 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hleft
    filter_upwards [hneigh] with z hz
    simp [continuedRoot,hz]
  · apply (interiorRoot_analyticAt_compactRight hright).congr
    have hneigh : ∀ᶠ z in 𝓝 W, |z.re| < 1 :=
      (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds hright
    filter_upwards [hneigh] with z hz
    have hn : ¬1 < z.re := by have := (abs_lt.mp hz).2; linarith
    simp [continuedRoot,hn]

theorem interiorRoot_five_quarters : interiorRoot (5/4:ℂ) = 2 := by
  rw [interiorRoot, inverseCosineRoot_inverse]
  have hn : (1-(5/4:ℂ)^2) = -(9/16:ℂ) := by norm_num
  rw [hn, Complex.sqrt_neg_of_nonneg (by constructor <;> norm_num : (0:ℂ) ≤ 9/16),
    Complex.sqrt_of_nonneg (by constructor <;> norm_num : (0:ℂ) ≤ 9/16)]
  norm_num [Real.sqrt_div, Real.sqrt_sq_eq_abs, Complex.I_sq]
  ring_nf
  norm_num [Complex.I_sq]

theorem compactLeftRoot_five_quarters : compactLeftRoot (5/4:ℂ) = 1/2 := by
  unfold compactLeftRoot
  norm_num only
  rw [Complex.sqrt_of_nonneg (by constructor <;> norm_num : (0:ℂ) ≤ 1/4),
    Complex.sqrt_of_nonneg (by constructor <;> norm_num : (0:ℂ) ≤ 9/4)]
  norm_num [Real.sqrt_div]

/-- Negative test against extending the upper-half-plane expression blindly. -/
theorem interiorRoot_not_continuousAt_five_quarters :
    ¬ ContinuousAt interiorRoot (5/4:ℂ) := by
  intro h
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp h (1/2) (by norm_num)
  let W : ℂ := (5/4:ℂ)+Complex.I*(δ/2:ℝ)
  have hW : 0 < W.im := by dsimp [W]; simp; linarith
  have hdist : dist W (5/4:ℂ) < δ := by
    simp [W, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hδ]
    linarith
  have hnear := hclose hdist
  rw [interiorRoot_five_quarters, dist_eq_norm] at hnear
  have hsmall := interiorRoot_norm_lt_one hW
  have htri := norm_sub_norm_le (2:ℂ) (interiorRoot W)
  rw [norm_sub_rev] at htri
  norm_num at htri
  linarith

end
end IsingBulk.Tail
