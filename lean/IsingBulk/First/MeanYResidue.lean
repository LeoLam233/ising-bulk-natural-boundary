import IsingBulk.First.MeanRectangleResidue

/-! The genuine Y=1 denominator, rather than only its linear principal part,
on the physically oriented mean rectangle. -/
namespace IsingBulk.First
noncomputable section
open Complex Set
open scoped Topology

def centeredMeanDenominator (v : ℂ) : ℂ := 1-Complex.exp (v*I)

@[simp] theorem centeredMeanDenominator_zero : centeredMeanDenominator 0 = 0 := by
  simp [centeredMeanDenominator]

theorem centeredMeanDenominator_hasDerivAt (v : ℂ) :
    HasDerivAt centeredMeanDenominator (-I*Complex.exp (v*I)) v := by
  simpa [centeredMeanDenominator, mul_comm] using!
    (((hasDerivAt_id v).mul_const I).cexp).const_sub 1

@[simp] theorem centeredMeanDenominator_deriv_zero : deriv centeredMeanDenominator 0 = -I := by
  simpa using (centeredMeanDenominator_hasDerivAt 0).deriv

/-- The mean chart is narrow enough that no other periodic Y pole occurs. -/
theorem centeredMeanDenominator_ne_zero {v : ℂ} (hv : v ≠ 0)
    (hr : |v.re| < 2*Real.pi) : centeredMeanDenominator v ≠ 0 := by
  intro hh
  have he : exp (v*I) = 1 := (sub_eq_zero.mp hh).symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
  have him := congrArg Complex.im hm
  simp at him
  have hlo : (-1:ℝ) < m := by
    have := (abs_lt.mp hr).1
    nlinarith [Real.pi_pos]
  have hhi : (m:ℝ) < 1 := by
    have := (abs_lt.mp hr).2
    nlinarith [Real.pi_pos]
  have hm0 : m=0 := by
    have hmlo : (-1:ℤ) < m := by exact_mod_cast hlo
    have hmhi : m < (1:ℤ) := by exact_mod_cast hhi
    omega
  rw [hm0] at hm
  have hv0 : v=0 := by simpa using hm
  exact hv hv0

theorem centeredMeanDenominator_slope_ne_zero {delta top bottom : ℝ}
    (hd : 0 < delta) (hdpi : delta < 2*Real.pi) {v : ℂ}
    (hv : v ∈ rectangleSet delta top bottom) : dslope centeredMeanDenominator 0 v ≠ 0 := by
  by_cases hv0 : v=0
  · simp [hv0]
  · have hr : |v.re| < 2*Real.pi := by
      have h := hv.1
      rw [uIcc_of_le (by linarith)] at h
      exact (abs_le.mpr h).trans_lt hdpi
    have hn := centeredMeanDenominator_ne_zero hv0 hr
    intro hz
    have he := sub_smul_dslope centeredMeanDenominator 0 v
    simp [hz] at he
    exact hn he.symm

/-- Cauchy residue for the exact denominator 1-exp(i v), with the positive
2*pi obtained from its actual derivative and the clockwise rectangle. -/
theorem clockwiseRectangle_centered_Y_residue {delta top bottom : ℝ} {f : ℂ → ℂ}
    (hd : 0 < delta) (hdpi : delta < 2*Real.pi) (ht : 0 < top) (hb : bottom < 0)
    (hf : DifferentiableOn ℂ f (rectangleSet delta top bottom)) :
    clockwiseRectangle delta top bottom (fun v => f v/centeredMeanDenominator v) =
      2*(Real.pi:ℂ)*f 0 := by
  let F : ℂ → ℂ := fun v => f v / dslope centeredMeanDenominator 0 v
  have hD : DifferentiableOn ℂ centeredMeanDenominator (rectangleSet delta top bottom) :=
    fun v _ => (centeredMeanDenominator_hasDerivAt v).differentiableAt.differentiableWithinAt
  have hds := (Complex.differentiableOn_dslope (rectangleSet_mem_nhds_zero hd ht hb)).mpr hD
  have hF : DifferentiableOn ℂ F (rectangleSet delta top bottom) :=
    hf.div hds (fun v hv => centeredMeanDenominator_slope_ne_zero hd hdpi hv)
  have he (v : ℂ) (hv : v ≠ 0) :
      f v/centeredMeanDenominator v = F v/v := by
    have h := sub_smul_dslope centeredMeanDenominator 0 v
    simp only [sub_zero, smul_eq_mul, centeredMeanDenominator_zero, sub_zero] at h
    dsimp [F]
    rw [← h]
    ring
  rw [clockwiseRectangle_congr_off_zero (ne_of_gt hd) (ne_of_gt ht) (ne_of_lt hb) he,
    clockwiseRectangle_simplePole hd ht hb hF]
  dsimp [F]
  simp only [dslope_same, centeredMeanDenominator_deriv_zero]
  field_simp

/-- Exact identification of the centered denominator after translating the
actual source product pole. -/
theorem meanProductY_translate_pole (N : ℕ) (rho alpha : ℝ) (w : ℂ)
    (hroot : exp (-(N:ℂ)*(alpha:ℂ)*I) = 1) :
    meanProductY N rho alpha (physicalMeanPole N rho+w) = exp (w*I) := by
  have he : meanProductY N rho alpha (physicalMeanPole N rho+w) =
      meanProductY N rho alpha (physicalMeanPole N rho)*exp (w*I) := by
    unfold meanProductY
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he, meanProductY_at_physicalMeanPole N rho alpha hroot, one_mul]

end
end IsingBulk.First
