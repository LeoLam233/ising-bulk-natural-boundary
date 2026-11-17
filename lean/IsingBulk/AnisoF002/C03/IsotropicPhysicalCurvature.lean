import IsingBulk.AnisoF002.C03.IsotropicActualOccupancyPhase

/-!
# The genuine second angular derivative of the canonical physical phase

The phase sine is identified with the same principal discriminant root
used by the physical spectral root. Differentiation of the original
dispersion then gives the full curvature numerator and cubic denominator.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric IsingBulk.AnisoF002.RegularTail

theorem upperPhysicalPhase_sin (W : ℂ) :
    Complex.sin (upperPhysicalPhase W) = Complex.sqrt (1 - W ^ 2) := by
  have he := Complex.cos_sub_sin_I (upperPhysicalPhase W)
  rw [upperPhysicalPhase_cos, neg_mul, upperPhysicalPhase_exp] at he
  unfold upperEdgeRoot at he
  have hh : Complex.sin (upperPhysicalPhase W) * Complex.I =
      Complex.I * Complex.sqrt (1 - W ^ 2) := sub_right_inj.mp he
  apply mul_right_cancel₀ Complex.I_ne_zero
  exact hh.trans (mul_comm _ _)

theorem upperPhysicalPhase_sine_re_pos (W : ℂ) (hW : 0 < W.im) :
    0 < (Complex.sin (upperPhysicalPhase W)).re := by
  rw [upperPhysicalPhase_sin]
  exact sqrt_re_pos_of_slit (edge_discriminant_slit (Or.inl hW))

theorem upperPhysicalPhase_sine_im_neg (W : ℂ) (hW : 0 < W.im) (hWr : 0 < W.re) :
    (Complex.sin (upperPhysicalPhase W)).im < 0 := by
  have hr := upperPhysicalPhase_sine_re_pos W hW
  have hs : Complex.sin (upperPhysicalPhase W) ^ 2 = 1 - W ^ 2 := by
    rw [Complex.sin_sq, upperPhysicalPhase_cos]
  have hi := congrArg Complex.im hs
  simp only [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im, zero_sub] at hi
  have hp := mul_pos hWr hW
  nlinarith only [hr, hi, hp]

def physicalPhaseNegativeCurvature (s w : ℂ) : ℂ :=
  s * (1 - Complex.cos w * Complex.cos (upperPhysicalPhase (isotropicDispersion (s, w)))) /
    Complex.sin (upperPhysicalPhase (isotropicDispersion (s, w))) ^ 3

/-- This is a derivative of the actual canonical phase slope, derived
from its stored first derivative and the original dispersion. -/
theorem physicalPhaseAngleSlope_hasDerivAt (s w : ℂ)
    (hW : 0 < (isotropicDispersion (s, w)).im) :
    HasDerivAt (physicalPhaseAngleSlope s) (-physicalPhaseNegativeCurvature s w) w := by
  let φ := upperPhysicalPhase (isotropicDispersion (s, w))
  have hsin : Complex.sin φ ≠ 0 := upperPhysicalPhase_sin_ne_zero _ hW
  have hd := ((Complex.hasDerivAt_sin w).neg).div
    ((physicalPhaseAngle_hasDerivAt s w hW).csin) hsin
  have hdisp : Complex.cos w + Complex.cos φ = s := by
    rw [upperPhysicalPhase_cos]
    simp only [isotropicDispersion, add_sub_cancel]
  have hnum := inverse_curvature_numerator w φ s hdisp
  convert hd using 1
  · rfl
  · dsimp only [physicalPhaseNegativeCurvature, physicalPhaseAngleSlope]
    change -(s * (1 - Complex.cos w * Complex.cos φ) / Complex.sin φ ^ 3) =
      (-Complex.cos w * Complex.sin φ - (-Complex.sin w) *
        (Complex.cos φ * (-Complex.sin w / Complex.sin φ))) / Complex.sin φ ^ 2
    rw [← hnum]
    field_simp [hsin]
    ring

theorem physicalPhaseNegativeCurvature_sqrt (s w : ℂ) :
    physicalPhaseNegativeCurvature s w =
      s * (1 - Complex.cos w * (s - Complex.cos w)) /
        Complex.sqrt (1 - (s - Complex.cos w) ^ 2) ^ 3 := by
  simp only [physicalPhaseNegativeCurvature, upperPhysicalPhase_cos, upperPhysicalPhase_sin,
    isotropicDispersion]

theorem physicalPhaseNegativeCurvature_analyticAt (q : ℂ × ℂ)
    (hW : 0 < (isotropicDispersion q).im) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => physicalPhaseNegativeCurvature p.1 p.2) q := by
  have hdisp : AnalyticAt ℂ isotropicDispersion q :=
    analyticAt_fst.sub (Complex.analyticAt_cos.comp analyticAt_snd)
  have hphase := (upperPhysicalPhase_analyticAt _ hW).comp hdisp
  exact (analyticAt_fst.mul (analyticAt_const.sub
    ((Complex.analyticAt_cos.comp analyticAt_snd).mul
      (Complex.analyticAt_cos.comp hphase)))).div
        ((Complex.analyticAt_sin.comp hphase).pow 3)
          (pow_ne_zero _ (upperPhysicalPhase_sin_ne_zero _ hW))

end IsingBulk.AnisoF002.Isotropic
