import IsingBulk.Tail.CompactRootContinuation
import IsingBulk.First.RadialDiskAdmissibility

/-! Quantitative attenuation of the actual physical quadratic root.
This converts a named upper support's imaginary dispersion margin into
exponential root contraction without a logarithmic branch assumption. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

theorem interiorRoot_gap_times_norm {W : ℂ} (hW : 0 < W.im) :
    W.im*‖interiorRoot W‖ ≤ 1-‖interiorRoot W‖ := by
  let z := interiorRoot W
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr (interiorRoot_nonzero W)
  have hr1 : ‖z‖ < 1 := interiorRoot_norm_lt_one hW
  have htrace := congrArg Complex.im (interiorRoot_trace W)
  change z.im+(z⁻¹).im=(2*W).im at htrace
  simp only [Complex.inv_im,Complex.mul_im] at htrace
  norm_num at htrace
  have hnormSq : Complex.normSq z=‖z‖^2 := Complex.normSq_eq_norm_sq z
  rw [hnormSq, neg_div] at htrace
  have htrace' : 2*W.im*‖z‖^2 = -z.im*(1-‖z‖^2) := by
    have hh := (div_eq_iff (ne_of_gt (sq_pos_of_pos hr0))).mp
      (show z.im/‖z‖^2=z.im-2*W.im by linarith)
    nlinarith
  have hi : -z.im ≤ ‖z‖ := (neg_le_abs z.im).trans (Complex.abs_im_le_norm z)
  have hmul := mul_le_mul_of_nonneg_right hi (show 0 ≤ 1-‖z‖^2 by nlinarith)
  have hbound : 2*W.im*‖z‖ ≤ 1-‖z‖^2 := by
    nlinarith
  change W.im*‖z‖ ≤ 1-‖z‖
  nlinarith [sq_nonneg (1-‖z‖)]

theorem interiorRoot_inverse_norm_le {W : ℂ} (hW : 0 < W.im) :
    ‖interiorRoot W‖⁻¹ ≤ 2*‖W‖+1 := by
  have he : (interiorRoot W)⁻¹=2*W-interiorRoot W := by
    linear_combination interiorRoot_trace W
  rw [← norm_inv,he]
  have h := norm_sub_le (2*W) (interiorRoot W)
  norm_num [norm_mul] at h
  have hi := interiorRoot_norm_lt_one hW
  linarith

theorem interiorRoot_modulus_gap {W : ℂ} (hW : 0 < W.im)
    {M : ℝ} (hM : ‖W‖ ≤ M) :
    W.im/(2*M+1) ≤ 1-‖interiorRoot W‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hD : 0 < 2*M+1 := by positivity
  have hr : 0 < ‖interiorRoot W‖ := norm_pos_iff.mpr (interiorRoot_nonzero W)
  have hin := interiorRoot_inverse_norm_le hW
  have hin' : ‖interiorRoot W‖⁻¹ ≤ 2*M+1 := by linarith
  have hscale := mul_le_mul_of_nonneg_right hin' hr.le
  rw [inv_mul_cancel₀ hr.ne'] at hscale
  have hgap := interiorRoot_gap_times_norm hW
  apply (div_le_iff₀ hD).mpr
  have h₁ := mul_le_mul_of_nonneg_left hscale hW.le
  have h₂ := mul_le_mul_of_nonneg_left hgap hD.le
  nlinarith

theorem interiorRoot_exponential_attenuation {W : ℂ} (hW : 0 < W.im)
    {M beta lam : ℝ} (hM : ‖W‖ ≤ M) (hmargin : beta*lam ≤ W.im) :
    ‖interiorRoot W‖ ≤ Real.exp (-(beta*lam)/(2*M+1)) := by
  have hD : 0 < 2*M+1 := by have := (norm_nonneg W).trans hM; positivity
  have hgap := interiorRoot_modulus_gap hW hM
  have hm := (div_le_div_of_nonneg_right hmargin hD.le).trans hgap
  have he := Real.add_one_le_exp (-(beta*lam)/(2*M+1))
  rw [neg_div] at he ⊢
  linarith

/-- The actual named upper point has p=1,m=0, hence this exact radius. -/
def upperAnchorY (c₀ eps τ lam θ : ℝ) : ℂ :=
  Complex.exp (((-c₀*eps-2*τ*lam:ℝ):ℂ)+(θ:ℂ)*Complex.I)

theorem radial_sourceS_norm_le_three (θ eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    ‖sourceS (radialParameter θ eps)‖ ≤ 3 := by
  have hi : (1+eps)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hn := norm_add_le (radialParameter θ eps) (radialParameter θ eps)⁻¹
  rw [norm_inv,radialParameter_norm heps] at hn
  change ‖radialParameter θ eps+(radialParameter θ eps)⁻¹‖ ≤ 3
  linarith

theorem radial_sourceS_im_nonneg (θ eps : ℝ) (heps : 0 ≤ eps)
    (hθ : 0 ≤ Real.sin θ) : 0 ≤ (sourceS (radialParameter θ eps)).im := by
  change 0 ≤ (radialParameter θ eps+(radialParameter θ eps)⁻¹).im
  rw [(radial_trace_components θ eps (by linarith)).2]
  have he : 2*eps-eps^2/(1+eps)=eps*(2+eps)/(1+eps) := by field_simp; ring
  rw [he]
  positivity

theorem upper_anchor_imaginary_margin (s : ℂ) {c₀ eps τ lam σ θ : ℝ}
    (hc : 0 ≤ c₀) (heps : 0 ≤ eps) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (hσ : 0 ≤ σ) (hθ : σ ≤ Real.sin θ) (hs : 0 ≤ (sourceS s).im) :
    2*τ*σ*lam ≤ (sourceW s (upperAnchorY c₀ eps τ lam θ)).im := by
  change 0 ≤ (s+s⁻¹).im at hs
  change 2*τ*σ*lam ≤ (IsingBulk.Branch.dispersion s (upperAnchorY c₀ eps τ lam θ)).im
  rw [upperAnchorY,polar_dispersion_im]
  have hneg : -c₀*eps-2*τ*lam=-(c₀*eps+2*τ*lam) := by ring
  rw [hneg,Real.sinh_neg]
  have hh := Real.self_le_sinh_iff.mpr (show 0 ≤ c₀*eps+2*τ*lam by positivity)
  have hmul := mul_le_mul_of_nonneg_right hh (hσ.trans hθ)
  have hmul' := mul_le_mul_of_nonneg_left hθ (show 0 ≤ 2*τ*lam by positivity)
  nlinarith [mul_nonneg (mul_nonneg hc heps) (hσ.trans hθ)]

theorem upper_anchor_norm_bound (θstar : ℝ) {c₀ eps τ lam θ : ℝ}
    (hc : 0 ≤ c₀) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ‖sourceW (radialParameter θstar eps) (upperAnchorY c₀ eps τ lam θ)‖ ≤
      4+Real.exp (c₀+2*τ) := by
  have hv : -c₀*eps-2*τ*lam ≤ 0 := by
    nlinarith [mul_nonneg hc heps,mul_nonneg hτ hlam]
  have hv' : c₀*eps+2*τ*lam ≤ c₀+2*τ := by nlinarith
  have hy : ‖upperAnchorY c₀ eps τ lam θ‖ ≤ 1 := by
    simp only [upperAnchorY,Complex.norm_exp,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    exact Real.exp_le_one_iff.mpr hv
  have hyi : ‖(upperAnchorY c₀ eps τ lam θ)⁻¹‖ ≤ Real.exp (c₀+2*τ) := by
    rw [upperAnchorY,← Complex.exp_neg,Complex.norm_exp]
    simp only [Complex.neg_re,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    apply Real.exp_le_exp.mpr
    linarith
  have hS := radial_sourceS_norm_le_three θstar eps heps heps1
  have hsum := norm_add_le (upperAnchorY c₀ eps τ lam θ) (upperAnchorY c₀ eps τ lam θ)⁻¹
  have hnorm := norm_sub_le (sourceS (radialParameter θstar eps))
    ((upperAnchorY c₀ eps τ lam θ+(upperAnchorY c₀ eps τ lam θ)⁻¹)/2)
  rw [norm_div] at hnorm
  norm_num at hnorm
  unfold sourceW
  nlinarith [Real.exp_pos (c₀+2*τ)]

/-- Quantitative named-anchor contraction uniform in eps, lambda and angle.
The fixed support margin σ and deformation τ determine the constant first. -/
theorem upper_anchor_exponential_attenuation (θstar : ℝ) {c₀ τ σ : ℝ}
    (hc : 0 ≤ c₀) (hτ : 0 < τ) (hσ : 0 < σ) (hθstar : 0 ≤ Real.sin θstar) :
    ∃ c : ℝ, 0 < c ∧ ∀ eps lam θ : ℝ,
      0 ≤ eps → eps ≤ 1 → 0 < lam → lam ≤ 1 → σ ≤ Real.sin θ →
      ‖globalRoot (radialParameter θstar eps) (upperAnchorY c₀ eps τ lam θ)‖ ≤
        Real.exp (-c*lam) := by
  let M := 4+Real.exp (c₀+2*τ)
  let c := 2*τ*σ/(2*M+1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hc' : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc',?_⟩
  intro eps lam θ heps heps1 hlam hlam1 hθ
  have him := upper_anchor_imaginary_margin (radialParameter θstar eps) hc heps hτ.le
    hlam.le hσ.le hθ (radial_sourceS_im_nonneg θstar eps heps hθstar)
  have him' : 0 < (sourceW (radialParameter θstar eps) (upperAnchorY c₀ eps τ lam θ)).im :=
    lt_of_lt_of_le (by positivity) him
  have hn := upper_anchor_norm_bound θstar hc heps heps1 hτ.le hlam.le hlam1 (θ := θ)
  have h := interiorRoot_exponential_attenuation him' hn him
  change ‖interiorRoot _‖ ≤ _
  convert h using 1
  congr 1
  dsimp [c,M]
  ring

end
end IsingBulk.Tail
