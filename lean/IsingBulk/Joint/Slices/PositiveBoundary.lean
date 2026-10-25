import IsingBulk.Joint.Slices.EdgeTransfer

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

/-- Slice obstruction is derived from the actual joint curve theorem. It is not
inferred from the ambient natural-boundary assertion. -/
theorem high_positive_slice_no_extension {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaH lam)) (hd : 0 < Anisotropic.spectralDet lam z)
    (hv : Anisotropic.spectralV lam z = 1) (hu : |Anisotropic.spectralU lam z| < 1)
    (hder : deriv (edgeMapV lam 1) z ≠ 0) (hprime : Anisotropic.spectralU lam z ∈ primePhaseCosines) :
    ¬ HasDomainExtension (omegaH lam) (Anisotropic.FormFactors.highNormalizedBulk lam) z := by
  have hS : S (ratioSlice lam z) ≠ 0 := spectralS_ne_zero_of_det_ne_zero hd.ne'
  have hp : p (ratioSlice lam z)^2 ≠ 1 := RegularEdges.product_sq_ne_one_of_strictU hd.ne' hu
  have hB : 0 < (Transverse.curveB (ratioSlice lam) z).im := by
    rw [Transverse.curveB,transferB_ratio_im]
    exact div_pos hd (Complex.normSq_pos.mpr hS)
  have he : Transverse.positiveParameter (Anisotropic.spectralU lam z) (ratioSlice lam z) = 0 := by
    rw [positiveParameter_ratio]
    have he := edgeMapV_at_endpoint hd.ne' hv
    simp only [Complex.ofReal_one] at he
    rw [he,sub_self]
  have heq : (fun t => Transverse.positiveParameter (Anisotropic.spectralU lam z) (ratioSlice lam t)) =
      fun t => edgeMapV lam 1 t-(Anisotropic.spectralU lam z:ℂ) :=
    funext (positiveParameter_ratio lam (Anisotropic.spectralU lam z))
  have hder' : deriv (fun t => Transverse.positiveParameter (Anisotropic.spectralU lam z) (ratioSlice lam t)) z ≠ 0 := by
    rw [heq,deriv_sub_const]
    exact hder
  have hno := Transverse.positive_high_curve_no_extension
    (FormFactors.ratioSlice_analyticAt lam z) (ratioSlice_high_frontier hlam hz) hS hp hB hu hprime he hder'
  rw [highDomain_pullback hlam] at hno
  rintro ⟨U,hU,hzU,g,hg,hgf⟩
  apply hno
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro w hw
  exact (hgf hw).trans (FormFactors.highNormalizedBulk_ratioSlice hlam hw.2).symm

theorem low_positive_slice_no_extension {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaL lam)) (hd : 0 < Anisotropic.spectralDet lam z)
    (hv : Anisotropic.spectralV lam z = 1) (hu : |Anisotropic.spectralU lam z| < 1)
    (hder : deriv (edgeMapV lam 1) z ≠ 0) (hprime : Anisotropic.spectralU lam z ∈ primePhaseCosines) :
    ¬ HasDomainExtension (omegaL lam) (Anisotropic.FormFactors.lowNormalizedBulk lam) z := by
  have hS : S (ratioSlice lam z) ≠ 0 := spectralS_ne_zero_of_det_ne_zero hd.ne'
  have hp : p (ratioSlice lam z)^2 ≠ 1 := RegularEdges.product_sq_ne_one_of_strictU hd.ne' hu
  have hB : 0 < (Transverse.curveB (ratioSlice lam) z).im := by
    rw [Transverse.curveB,transferB_ratio_im]
    exact div_pos hd (Complex.normSq_pos.mpr hS)
  have he : Transverse.positiveParameter (Anisotropic.spectralU lam z) (ratioSlice lam z) = 0 := by
    rw [positiveParameter_ratio]
    have he := edgeMapV_at_endpoint hd.ne' hv
    simp only [Complex.ofReal_one] at he
    rw [he,sub_self]
  have heq : (fun t => Transverse.positiveParameter (Anisotropic.spectralU lam z) (ratioSlice lam t)) =
      fun t => edgeMapV lam 1 t-(Anisotropic.spectralU lam z:ℂ) :=
    funext (positiveParameter_ratio lam (Anisotropic.spectralU lam z))
  have hder' : deriv (fun t => Transverse.positiveParameter (Anisotropic.spectralU lam z) (ratioSlice lam t)) z ≠ 0 := by
    rw [heq,deriv_sub_const]
    exact hder
  have hno := Transverse.positive_low_curve_no_extension
    (FormFactors.ratioSlice_analyticAt lam z) (ratioSlice_low_frontier hlam hz) hS hp hB hu hprime he hder'
  rw [lowDomain_pullback hlam] at hno
  rintro ⟨U,hU,hzU,g,hg,hgf⟩
  apply hno
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro w hw
  exact (hgf hw).trans (FormFactors.lowNormalizedBulk_ratioSlice hlam hw.2).symm

end
end IsingBulk.Joint
