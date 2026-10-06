import IsingBulk.Analysis.BranchLocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! Explicit logarithmic realization of the fourth-quadrant inverse cosine.
This removes a branch-choice ambiguity but does not yet give uniform jets. -/
namespace IsingBulk.Branch
noncomputable section

def inverseCosineRoot (W : ℂ) : ℂ := W+Complex.I*Complex.sqrt (1-W^2)

theorem sqrt_sq (z : ℂ) : (Complex.sqrt z)^2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2:ℕ) ≠ 0)

theorem inverseCosineRoot_inverse (W : ℂ) :
    (inverseCosineRoot W)⁻¹ = W-Complex.I*Complex.sqrt (1-W^2) := by
  have hprod : inverseCosineRoot W * (W-Complex.I*Complex.sqrt (1-W^2)) = 1 := by
    unfold inverseCosineRoot
    calc
      _ = W^2-Complex.I^2*(Complex.sqrt (1-W^2))^2 := by ring
      _ = 1 := by rw [Complex.I_sq, sqrt_sq]; ring
  exact inv_eq_of_mul_eq_one_right hprod

theorem inverseCosineRoot_ne_zero (W : ℂ) : inverseCosineRoot W ≠ 0 := by
  intro h
  have := inverseCosineRoot_inverse W
  rw [h, inv_zero] at this
  have he : W+Complex.I*Complex.sqrt (1-W^2) = 0 := h
  have hw : W = 0 := by linear_combination (he - this)/2
  subst W
  simp [inverseCosineRoot] at h

theorem inverseCosineRoot_trace (W : ℂ) :
    inverseCosineRoot W+(inverseCosineRoot W)⁻¹ = 2*W := by
  rw [inverseCosineRoot_inverse, inverseCosineRoot]
  ring

def lowerArccos (W : ℂ) : ℂ := -Complex.I*Complex.log (inverseCosineRoot W)

theorem cos_lowerArccos (W : ℂ) : Complex.cos (lowerArccos W) = W := by
  have he : lowerArccos W * Complex.I = Complex.log (inverseCosineRoot W) := by
    unfold lowerArccos
    calc
      _ = -(Complex.I*Complex.I)*Complex.log (inverseCosineRoot W) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Complex.cos, he, neg_mul, he, Complex.exp_neg,
    Complex.exp_log (inverseCosineRoot_ne_zero W), inverseCosineRoot_trace]
  ring

theorem inverseCosineRoot_quadrant (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im) :
    0 < (inverseCosineRoot W).re ∧ 0 < (inverseCosineRoot W).im := by
  have hs : (1-W^2).im < 0 := by
    simp [pow_two, Complex.mul_im]
    nlinarith [mul_pos hre him]
  obtain ⟨hr, hi⟩ := sqrt_lower_orientation (1-W^2) hs
  simp only [inverseCosineRoot, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, Complex.add_im, Complex.mul_im]
  constructor <;> linarith

theorem inverseCosineRoot_norm (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im) :
    1 < ‖inverseCosineRoot W‖ := by
  let z := inverseCosineRoot W
  have hz : 0 < z.im := (inverseCosineRoot_quadrant W hre him).2
  have ht := congrArg Complex.im (inverseCosineRoot_trace W)
  change z.im + (z⁻¹).im = (2*W).im at ht
  simp [Complex.inv_im, Complex.mul_im, neg_div] at ht
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr (inverseCosineRoot_ne_zero W)
  have ht' := (div_eq_iff (ne_of_gt hn)).mp
    (show z.im / Complex.normSq z = z.im-2*W.im by linarith)
  have hns : 1 < Complex.normSq z := by
    by_contra h
    have hle : Complex.normSq z ≤ 1 := le_of_not_gt h
    nlinarith [mul_pos him hn]
  exact Complex.one_lt_normSq_iff.mp hns

/-- The explicit branch solves cos φ=W and has the manuscript's orientation. -/
theorem lowerArccos_sheet (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im) :
    Complex.cos (lowerArccos W) = W ∧
    0 < (lowerArccos W).re ∧ (lowerArccos W).re < Real.pi/2 ∧
    (lowerArccos W).im < 0 := by
  refine ⟨cos_lowerArccos W, ?_⟩
  obtain ⟨hzr, hzi⟩ := inverseCosineRoot_quadrant W hre him
  have harg : 0 < Complex.arg (inverseCosineRoot W) := by
    have hn := Complex.arg_nonneg_iff.mpr (le_of_lt hzi)
    have hne : Complex.arg (inverseCosineRoot W) ≠ 0 := by
      intro h
      have := (Complex.arg_eq_zero_iff.mp h).2
      linarith
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have harglt := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzr)
  have hlog := Real.log_pos (inverseCosineRoot_norm W hre him)
  simpa [lowerArccos, Complex.mul_re, Complex.mul_im, Complex.log_re,
    Complex.log_im] using And.intro harg (And.intro harglt (neg_neg_of_pos hlog))

theorem lowerArccos_differentiable (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im) :
    DifferentiableAt ℂ lowerArccos W := by
  have hs : (1-W^2).im < 0 := by
    simp [pow_two, Complex.mul_im]
    nlinarith [mul_pos hre him]
  have hp : DifferentiableAt ℂ (fun z : ℂ => 1-z^2) W :=
    (differentiableAt_id.pow 2).const_sub 1
  have houter : DifferentiableAt ℂ Complex.sqrt (1-W^2) :=
    Complex.differentiableAt_sqrt (Or.inr (ne_of_lt hs))
  have hsq : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (1-z^2)) W :=
    DifferentiableAt.comp (f := fun z : ℂ => 1-z^2) (g := Complex.sqrt) W houter hp
  have hz : DifferentiableAt ℂ inverseCosineRoot W :=
    differentiableAt_id.add (hsq.const_mul Complex.I)
  have hl := DifferentiableAt.comp (f := inverseCosineRoot) (g := Complex.log) W
    (Complex.differentiableAt_log (z := inverseCosineRoot W)
    (Or.inl (inverseCosineRoot_quadrant W hre him).1)) hz
  exact hl.const_mul (-Complex.I)

theorem lowerArccos_deriv (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im) :
    deriv lowerArccos W = -1 / Complex.sin (lowerArccos W) := by
  have hd := (lowerArccos_differentiable W hre him).hasDerivAt.ccos
  have heq : (fun z => Complex.cos (lowerArccos z)) = id := funext cos_lowerArccos
  rw [heq] at hd
  have hv := hd.unique (hasDerivAt_id W)
  have hn : Complex.sin (lowerArccos W) ≠ 0 := by
    intro h; simp [h] at hv
  apply (eq_div_iff hn).mpr
  linear_combination -hv

/-- Exact derivative size before any uniform asymptotic comparison. -/
theorem lowerArccos_deriv_norm (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im) :
    ‖deriv lowerArccos W‖ = (Real.sqrt ‖1-W^2‖)⁻¹ := by
  have hs : (Complex.sin (lowerArccos W))^2 = 1-W^2 := by
    have h := Complex.sin_sq_add_cos_sq (lowerArccos W)
    rw [cos_lowerArccos] at h
    linear_combination h
  have hn : Real.sqrt ‖1-W^2‖ = ‖Complex.sin (lowerArccos W)‖ := by
    rw [← hs, norm_pow, Real.sqrt_sq (norm_nonneg _)]
  rw [lowerArccos_deriv W hre him, norm_div, norm_neg, norm_one, one_div, hn]

/-- Uniqueness on the fourth-quadrant sheet makes the representation bridge
explicit: another angle with this range and cosine has exactly this value. -/
theorem lowerArccos_unique (W φ : ℂ) (hre : 0 < W.re) (him : 0 < W.im)
    (hc : Complex.cos φ = W) (hφr : 0 < φ.re) (hφr' : φ.re < Real.pi/2)
    (hφi : φ.im < 0) : φ = lowerArccos W := by
  obtain ⟨_, hψr, hψr', hψi⟩ := lowerArccos_sheet W hre him
  obtain ⟨k, hk | hk⟩ := Complex.cos_eq_cos_iff.mp (hc.trans (cos_lowerArccos W).symm)
  · have hr := congrArg Complex.re hk
    simp at hr
    have hklo : (-1:ℝ) < k := by nlinarith [Real.pi_pos]
    have hkhi : (k:ℝ) < 1 := by nlinarith [Real.pi_pos]
    have hk0 : k = 0 := by
      have : (-1:ℤ) < k := by exact_mod_cast hklo
      have : k < (1:ℤ) := by exact_mod_cast hkhi
      omega
    simpa [hk0] using hk.symm
  · have hi := congrArg Complex.im hk
    simp at hi
    linarith

end
end IsingBulk.Branch
