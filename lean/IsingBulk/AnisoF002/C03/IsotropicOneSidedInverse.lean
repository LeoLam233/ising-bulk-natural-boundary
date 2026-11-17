import IsingBulk.AnisoF002.C03.IsotropicRightImage

/-!
# One explicit inverse on the entire limiting one-sided arc

The same logarithmic arccosine used on the right interval also realizes
the left inverse. The proof uses the original unsquared dispersion and
the physical boundary phase. No independently chosen local inverses or
historical isotropic endpoint are used.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric
open IsingBulk.AnisoF002.RegularTail

set_option maxHeartbeats 800000

theorem square_mem_slitPlane_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    z ^ 2 ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hi : z.im = 0
  · left
    simpa [pow_two, Complex.mul_re, hi] using sq_pos_of_pos hz
  · right
    simp only [pow_two, Complex.mul_im]
    intro he
    have hm : z.re * z.im ≠ 0 := mul_ne_zero (ne_of_gt hz) hi
    apply hm
    nlinarith

theorem complex_sine_re_pos_strip (A : ℂ) (hA : 0 < A.re ∧ A.re < Real.pi) :
    0 < (Complex.sin A).re := by
  rw [Complex.sin_eq]
  simpa [Complex.sin_ofReal_re] using
    mul_pos (Real.sin_pos_of_pos_of_lt_pi hA.1 hA.2) (Real.cosh_pos A.im)

theorem rightArcCos_cos_strip (A : ℂ) (hA : 0 < A.re ∧ A.re < Real.pi) :
    rightArcCos (Complex.cos A) = A ∧ AnalyticAt ℂ rightArcCos (Complex.cos A) := by
  have hsin := complex_sine_re_pos_strip A hA
  have hsq : 1 - Complex.cos A ^ 2 ∈ Complex.slitPlane := by
    rw [← Complex.sin_sq]
    exact square_mem_slitPlane_of_re_pos _ hsin
  have hsqrt : Complex.sqrt (1 - Complex.cos A ^ 2) = Complex.sin A := by
    have hp : Complex.sqrt (1 - Complex.cos A ^ 2) ^ 2 = Complex.sin A ^ 2 := by
      rw [Complex.sin_sq]
      simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (1 - Complex.cos A ^ 2) 2
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hp) with he | he
    · exact he
    · have hr := sqrt_re_pos_of_slit hsq
      have her := congrArg Complex.re he
      simp only [Complex.neg_re] at her
      linarith
  have harg : rightArcCosArgument (Complex.cos A) = Complex.exp (A * Complex.I) := by
    rw [rightArcCosArgument, hsqrt, Complex.exp_mul_I]
    ring
  have hargslit : rightArcCosArgument (Complex.cos A) ∈ Complex.slitPlane := by
    rw [harg]
    apply Complex.mem_slitPlane_iff.mpr
    right
    apply ne_of_gt
    rw [Complex.exp_im]
    simp only [Complex.mul_im, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hA.1 hA.2)
  refine ⟨?_, rightArcCos_analyticAt _ hsq hargslit⟩
  unfold rightArcCos
  rw [harg, Complex.log_exp (by simpa using (show -Real.pi < A.re by linarith [Real.pi_pos]))
    (by simpa using hA.2.le)]
  calc
    -Complex.I * (A * Complex.I) = -A * (Complex.I ^ 2) := by ring
    _ = A := by rw [Complex.I_sq]; ring

theorem upperBoundaryPhase_cos (x : ℝ) (hx : -1 < x) :
    Complex.cos (upperBoundaryPhase x) = (x : ℂ) := by
  have hr := upperBoundaryRoot_ne_zero x hx
  have hp := (upperBoundaryRoot_spec x hx).1
  have he : Complex.exp (-(upperBoundaryPhase x * Complex.I)) = upperBoundaryRoot x := by
    have hh : -(upperBoundaryPhase x * Complex.I) = Complex.log (upperBoundaryRoot x) := by
      unfold upperBoundaryPhase
      linear_combination -(Complex.log (upperBoundaryRoot x)) * Complex.I_sq
    rw [hh, Complex.exp_log hr]
  have hi : Complex.exp (upperBoundaryPhase x * Complex.I) = (upperBoundaryRoot x)⁻¹ := by
    rw [← he, Complex.exp_neg, inv_inv]
  rw [Complex.cos, hi, neg_mul, he]
  field_simp
  linear_combination hp

theorem upperBoundaryPhase_re_zero (x : ℝ) (hx : 1 ≤ x) :
    (upperBoundaryPhase x).re = 0 := by
  have hz : Real.sqrt (1 - x ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith)
  have him : (upperBoundaryRoot x).im = 0 := by simp [upperBoundaryRoot, hz]
  have hreal : upperBoundaryRoot x = ((upperBoundaryRoot x).re : ℂ) :=
    Complex.ext rfl (by simpa using him)
  have hpos : 0 < (upperBoundaryRoot x).re := by
    rcases Complex.mem_slitPlane_iff.mp (upperBoundaryRoot_spec x (by linarith)).2.2.1 with h | h
    · exact h
    · exact False.elim (h him)
  unfold upperBoundaryPhase
  rw [hreal, ← Complex.ofReal_log hpos.le]
  simp

theorem upperBoundaryPhase_re_range (x : ℝ) (hx : -1 < x) :
    0 ≤ (upperBoundaryPhase x).re ∧ (upperBoundaryPhase x).re < Real.pi := by
  by_cases hx1 : x ≤ 1
  · rw [upperBoundaryPhase_eq_arccos x hx hx1]
    simpa only [Complex.ofReal_re] using And.intro (Real.arccos_nonneg x) (Real.arccos_lt_pi.mpr hx)
  · rw [upperBoundaryPhase_re_zero x (le_of_not_ge hx1)]
    exact ⟨le_rfl, Real.pi_pos⟩

def oneSidedBoundaryCoordinate (S w : ℝ) : ℂ :=
  (w : ℂ) + upperBoundaryPhase (S - Real.cos w)

theorem oneSidedBoundaryCoordinate_continuous (S : ℝ) (hS : 0 < S) :
    Continuous (oneSidedBoundaryCoordinate S) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hx : -1 < S - Real.cos w := by linarith [Real.cos_le_one w]
  exact Complex.continuous_ofReal.continuousAt.add
    ((upperBoundaryPhase_continuousAt _ hx).comp
      (f := fun x : ℝ => S - Real.cos x) (continuous_const.sub Real.continuous_cos).continuousAt)

theorem oneSidedBoundary_dispersion (S w : ℝ) (hS : 0 < S) :
    Complex.cos (w : ℂ) +
      Complex.cos (oneSidedBoundaryCoordinate S w - (w : ℂ)) = (S : ℂ) := by
  have hx : -1 < S - Real.cos w := by linarith [Real.cos_le_one w]
  rw [oneSidedBoundaryCoordinate, add_sub_cancel_left, upperBoundaryPhase_cos _ hx]
  simp

theorem oneSidedBoundary_half_difference_strip (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-Real.pi) 0) :
    0 < ((upperBoundaryPhase (S - Real.cos w) - (w : ℂ)) / 2).re ∧
      ((upperBoundaryPhase (S - Real.cos w) - (w : ℂ)) / 2).re < Real.pi := by
  have hx : -1 < S - Real.cos w := by linarith [hS.1, Real.cos_le_one w]
  have hφ := upperBoundaryPhase_re_range (S - Real.cos w) hx
  have hre : ((upperBoundaryPhase (S - Real.cos w) - (w : ℂ)) / 2).re =
      ((upperBoundaryPhase (S - Real.cos w)).re - w) / 2 := by simp
  rw [hre]
  constructor
  · by_cases hw0 : w = 0
    · subst w
      have hx1 : S - Real.cos 0 < 1 := by simpa using (show S - 1 < 1 by linarith [hS.2])
      rw [upperBoundaryPhase_eq_arccos _ hx hx1.le, Complex.ofReal_re]
      have hg := Real.arccos_pos.mpr hx1
      linarith
    · have hwneg : w < 0 := lt_of_le_of_ne hw.2 hw0
      linarith [hφ.1]
  · linarith [hφ.2, hw.1]

/-- The original right inverse realizes the complete left and right
limiting one-sided arc, and is analytic with nonzero regular denominator
at every point including the branch and the endpoint at -pi. -/
theorem explicitRightInverse_on_oneSided_arc (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-Real.pi) 0) :
    explicitRightInverse ((S : ℂ), oneSidedBoundaryCoordinate S w) = (w : ℂ) ∧
      AnalyticAt ℂ explicitRightInverse ((S : ℂ), oneSidedBoundaryCoordinate S w) ∧
      Complex.cos (oneSidedBoundaryCoordinate S w / 2) ≠ 0 ∧
      explicitRightDenominator ((S : ℂ), oneSidedBoundaryCoordinate S w) ≠ 0 := by
  let φ := upperBoundaryPhase (S - Real.cos w)
  let v := oneSidedBoundaryCoordinate S w
  let A := (φ - (w : ℂ)) / 2
  have hA : 0 < A.re ∧ A.re < Real.pi := oneSidedBoundary_half_difference_strip S w hS hw
  have hdisp := oneSidedBoundary_dispersion S w hS.1
  have hhalf : (S : ℂ) = 2 * Complex.cos (v / 2) * Complex.cos A := by
    rw [← hdisp, Complex.cos_add_cos]
    have hs : ((w : ℂ) + (v - (w : ℂ))) / 2 = v / 2 := by ring
    have hd : ((w : ℂ) - (v - (w : ℂ))) / 2 = -A := by
      dsimp [v, A, φ, oneSidedBoundaryCoordinate]
      ring
    change 2 * Complex.cos (((w : ℂ) + (v - (w : ℂ))) / 2) *
      Complex.cos (((w : ℂ) - (v - (w : ℂ))) / 2) = _
    rw [hs, hd, Complex.cos_neg]
  have hc : Complex.cos (v / 2) ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_mul] at hhalf
    exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hS.1)) hhalf
  have hratio : (S : ℂ) / (2 * Complex.cos (v / 2)) = Complex.cos A := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hc)).mpr
    rw [hhalf]
    ring
  have harc := rightArcCos_cos_strip A hA
  have hu : explicitRightInverse ((S : ℂ), v) = (w : ℂ) := by
    rw [explicitRightInverse, hratio, harc.1]
    dsimp [v, A, φ, oneSidedBoundaryCoordinate]
    ring
  have han : AnalyticAt ℂ explicitRightInverse ((S : ℂ), v) := by
    exact explicitRightInverse_analyticAt ((S : ℂ), v) hc (by simpa only [hratio] using harc.2)
  refine ⟨hu, han, hc, ?_⟩
  change explicitRightDenominator ((S : ℂ), v) ≠ 0
  rw [explicitRightDenominator, hu]
  have he : v - (w : ℂ) = φ := by dsimp [v, φ, oneSidedBoundaryCoordinate]; ring
  rw [he, Complex.sin_sub_sin]
  have hv : (φ + (w : ℂ)) / 2 = v / 2 := by dsimp [v, φ, oneSidedBoundaryCoordinate]; ring
  rw [hv]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (ne_of_apply_ne Complex.re (ne_of_gt (complex_sine_re_pos_strip A hA)))) hc

end IsingBulk.AnisoF002.Isotropic
