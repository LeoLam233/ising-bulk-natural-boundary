import IsingBulk.Joint.Slices.PositiveBoundary

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

theorem low_negative_slice_no_extension {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaL lam)) (hd : Anisotropic.spectralDet lam z < 0)
    (hv : Anisotropic.spectralV lam z = -1) (hu : |Anisotropic.spectralU lam z| < 1)
    (hder : deriv (edgeMapV lam (-1)) z ≠ 0) (hprime : Anisotropic.spectralU lam z ∈ primePhaseCosines) :
    ¬ HasDomainExtension (omegaL lam) (Anisotropic.FormFactors.lowNormalizedBulk lam) z := by
  have hS : S (ratioSlice lam z) ≠ 0 := spectralS_ne_zero_of_det_ne_zero hd.ne
  have hp : p (ratioSlice lam z)^2 ≠ 1 := RegularEdges.product_sq_ne_one_of_strictU hd.ne hu
  have hB : 0 < (Transverse.negativeCurveB (ratioSlice lam) z).im := by
    rw [Transverse.negativeCurveB,Complex.neg_im,transferB_ratio_im]
    exact neg_pos.mpr (div_neg_of_neg_of_pos hd (Complex.normSq_pos.mpr hS))
  have he : Transverse.negativeParameter (Anisotropic.spectralU lam z) (ratioSlice lam z) = 0 := by
    rw [negativeParameter_ratio]
    have he := edgeMapV_at_endpoint hd.ne hv
    simp only [Complex.ofReal_neg,Complex.ofReal_one] at he
    rw [he,sub_self]
  have heq : (fun t => Transverse.negativeParameter (Anisotropic.spectralU lam z) (ratioSlice lam t)) =
      fun t => edgeMapV lam (-1) t-(Anisotropic.spectralU lam z:ℂ) :=
    funext (negativeParameter_ratio lam (Anisotropic.spectralU lam z))
  have hder' : deriv (fun t => Transverse.negativeParameter (Anisotropic.spectralU lam z) (ratioSlice lam t)) z ≠ 0 := by
    rw [heq,deriv_sub_const]
    exact hder
  have hno := Transverse.negative_even_low_curve_no_extension
    (FormFactors.ratioSlice_analyticAt lam z) (ratioSlice_low_frontier hlam hz) hS hp hB hu hprime he hder'
  rw [lowDomain_pullback hlam] at hno
  rintro ⟨U,hU,hzU,g,hg,hgf⟩
  apply hno
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro w hw
  exact (hgf hw).trans (FormFactors.lowNormalizedBulk_ratioSlice hlam hw.2).symm

end
end IsingBulk.Joint
