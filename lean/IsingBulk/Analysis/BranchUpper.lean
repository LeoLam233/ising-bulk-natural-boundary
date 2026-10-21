import IsingBulk.Analysis.BranchSheet
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The existing explicit lower inverse-cosine branch on the full upper
half-plane. All earlier fourth-quadrant statements remain unchanged. -/
namespace IsingBulk.Branch
noncomputable section
open Complex
open scoped Topology

theorem sqrt_re_nonneg_all (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simp <;> positivity

theorem inverseCosineRoot_im_pos_of_upper {W : ℂ} (hW : 0 < W.im) :
    0 < (inverseCosineRoot W).im := by
  have hs := sqrt_re_nonneg_all (1-W^2)
  simp only [inverseCosineRoot,Complex.add_im,Complex.mul_im,Complex.I_re,
    Complex.I_im,zero_mul,one_mul,zero_add]
  linarith

theorem inverseCosineRoot_norm_of_upper {W : ℂ} (hW : 0 < W.im) :
    1 < ‖inverseCosineRoot W‖ := by
  let z := inverseCosineRoot W
  have hz : 0 < z.im := inverseCosineRoot_im_pos_of_upper hW
  have ht := congrArg Complex.im (inverseCosineRoot_trace W)
  change z.im+(z⁻¹).im = (2*W).im at ht
  simp [Complex.inv_im,Complex.mul_im,neg_div] at ht
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr (inverseCosineRoot_ne_zero W)
  have ht' := (div_eq_iff (ne_of_gt hn)).mp
    (show z.im/Complex.normSq z = z.im-2*W.im by linarith)
  have hns : 1 < Complex.normSq z := by
    by_contra h
    have hle : Complex.normSq z ≤ 1 := le_of_not_gt h
    nlinarith [mul_pos hW hn]
  exact Complex.one_lt_normSq_iff.mp hns

/-- The same literal branch lies in the lower strip 0<Re phi<pi. -/
theorem lowerArccos_sheet_of_upper {W : ℂ} (hW : 0 < W.im) :
    cos (lowerArccos W) = W ∧ 0 < (lowerArccos W).re ∧
      (lowerArccos W).re < Real.pi ∧ (lowerArccos W).im < 0 := by
  have hzi := inverseCosineRoot_im_pos_of_upper hW
  have harg : 0 < arg (inverseCosineRoot W) := by
    have hn := Complex.arg_nonneg_iff.mpr hzi.le
    have hne : arg (inverseCosineRoot W) ≠ 0 := by
      intro h
      have := (Complex.arg_eq_zero_iff.mp h).2
      linarith
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have harglt := Complex.arg_lt_pi_iff.mpr (Or.inr hzi.ne')
  have hlog := Real.log_pos (inverseCosineRoot_norm_of_upper hW)
  refine ⟨cos_lowerArccos W,?_⟩
  simpa [lowerArccos,Complex.mul_re,Complex.mul_im,Complex.log_re,Complex.log_im]
    using And.intro harg (And.intro harglt (neg_neg_of_pos hlog))

theorem lowerArccos_analytic_of_slit (W : ℂ)
    (hs : 1-W^2 ∈ Complex.slitPlane)
    (hl : inverseCosineRoot W ∈ Complex.slitPlane) : AnalyticAt ℂ lowerArccos W := by
  have hsqrt : AnalyticAt ℂ Complex.sqrt (1-W^2) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hs)
  have hpoly : AnalyticAt ℂ (fun z : ℂ => 1-z^2) W := by fun_prop
  have hroot : AnalyticAt ℂ inverseCosineRoot W :=
    analyticAt_id.add (analyticAt_const.mul (AnalyticAt.comp
      (f := fun z : ℂ => 1-z^2) (g := Complex.sqrt) hsqrt hpoly))
  have hlog : AnalyticAt ℂ Complex.log (inverseCosineRoot W) :=
    analyticAt_clog hl
  exact analyticAt_const.mul (AnalyticAt.comp
    (f := inverseCosineRoot) (g := Complex.log) hlog hroot)


theorem lowerArccos_analytic_of_upper {W : ℂ} (hW : 0 < W.im) :
    AnalyticAt ℂ lowerArccos W := by
  apply lowerArccos_analytic_of_slit
  · by_cases hr : W.re = 0
    · left
      simp only [Complex.sub_re,Complex.one_re,pow_two,Complex.mul_re,hr,zero_mul]
      nlinarith [sq_nonneg W.im]
    · right
      intro hz
      simp only [Complex.sub_im,Complex.one_im,pow_two,Complex.mul_im] at hz
      have hp := mul_ne_zero hr hW.ne'
      apply hp
      nlinarith
  · exact Or.inr (inverseCosineRoot_im_pos_of_upper hW).ne'


end
end IsingBulk.Branch
