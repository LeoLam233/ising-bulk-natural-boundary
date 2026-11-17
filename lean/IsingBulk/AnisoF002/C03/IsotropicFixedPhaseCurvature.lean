import IsingBulk.AnisoF002.C03.IsotropicBranchCurvature

/-!
# The genuine fixed-population phase curvature on the entire contour

Both derivatives of the smooth balanced angular map are retained.
The first derivative of the phase along that map is differentiated
before any population derivatives are restored by the separate exact
constraint formula.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric Filter IsingBulk.AnisoF002.RegularTail

def fixedOccupancySecondSlope (η τ ρ υ θ : ℝ) : ℂ :=
  -Complex.I * ((τ * (ρ * deriv (deriv (lowerPeriodicBump η)) θ -
    υ * deriv (deriv (upperPeriodicBump η)) θ) : ℝ) : ℂ)

theorem fixedOccupancySlope_hasDerivAt (η τ ρ υ θ : ℝ) :
    HasDerivAt (fixedOccupancySlope η τ ρ υ) (fixedOccupancySecondSlope η τ ρ υ θ) θ := by
  have hp := (upperPeriodicBump_contDiff η (n := 2)).deriv'.differentiable_one θ |>.hasDerivAt
  have hm := (lowerPeriodicBump_contDiff η (n := 2)).deriv'.differentiable_one θ |>.hasDerivAt
  have hd := ((hm.const_mul ρ).sub (hp.const_mul υ)).const_mul τ |>.ofReal_comp
  convert! (hasDerivAt_const θ (1 : ℂ)).sub (hd.const_mul Complex.I) using 1
  simp only [fixedOccupancySecondSlope, zero_sub, neg_mul]

def fixedOccupancyPhaseSlope (s : ℂ) (η τ ρ υ θ : ℝ) : ℂ :=
  physicalPhaseAngleSlope s (fixedOccupancyAngle η τ ρ υ θ) * fixedOccupancySlope η τ ρ υ θ

def fixedOccupancyPhaseCurvature (s : ℂ) (η τ ρ υ θ : ℝ) : ℂ :=
  physicalPhaseNegativeCurvature s (fixedOccupancyAngle η τ ρ υ θ) *
      fixedOccupancySlope η τ ρ υ θ ^ 2 -
    physicalPhaseAngleSlope s (fixedOccupancyAngle η τ ρ υ θ) * fixedOccupancySecondSlope η τ ρ υ θ

theorem fixedOccupancyPhaseSlope_hasDerivAt (s : ℂ) (hs : 0 < s.im)
    (η τ ρ υ θ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hυ : 0 ≤ υ) :
    HasDerivAt (fixedOccupancyPhaseSlope s η τ ρ υ)
      (-fixedOccupancyPhaseCurvature s η τ ρ υ θ) θ := by
  have hsheet := fixedOccupancyAngle_sheet s hs η τ ρ υ θ hη hτ hρ hυ
  have hd := (physicalPhaseAngleSlope_hasDerivAt s (fixedOccupancyAngle η τ ρ υ θ) hsheet).scomp θ
    (fixedOccupancyAngle_hasDerivAt η τ ρ υ θ)
  have hp := hd.mul (fixedOccupancySlope_hasDerivAt η τ ρ υ θ)
  convert! hp using 1
  simp only [fixedOccupancyPhaseCurvature, smul_eq_mul, Function.comp_apply]
  ring

theorem fixedOccupancyPhaseCurvature_on_branch (s : ℂ) (b η τ ρ υ u : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hu : |u| < η) :
    fixedOccupancyPhaseCurvature s η τ ρ υ (-b + u) =
      physicalPhaseNegativeCurvature s (((-b + u : ℝ) : ℂ) - Complex.I * ((τ * ρ : ℝ) : ℂ)) := by
  obtain ⟨hp, hm⟩ := lower_branch_plateau_derivatives b η u hη hwidth hu
  have hnear : ∀ᶠ x in 𝓝 (-b + u), |x + b| < η := by
    have hc : ContinuousAt (fun x : ℝ => |x + b|) (-b + u) := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa only [show -b + u + b = u by ring] using hu))
  have hpd : deriv (upperPeriodicBump η) =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_derivatives b η (x + b) hη hwidth hx).1
    rwa [show -b + (x + b) = x by ring] at hh
  have hmd : deriv (lowerPeriodicBump η) =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_derivatives b η (x + b) hη hwidth hx).2
    rwa [show -b + (x + b) = x by ring] at hh
  have hp2 : deriv (deriv (upperPeriodicBump η)) (-b + u) = 0 := by
    simpa only [deriv_const] using hpd.deriv_eq
  have hm2 : deriv (deriv (lowerPeriodicBump η)) (-b + u) = 0 := by
    simpa only [deriv_const] using hmd.deriv_eq
  simp only [fixedOccupancyPhaseCurvature, fixedOccupancySlope, fixedOccupancySecondSlope,
    hp, hm, hp2, hm2, mul_zero, sub_zero, Complex.ofReal_zero, one_pow, mul_one]
  rw [fixedOccupancyAngle_on_branch b η τ ρ υ u hη hwidth hu.le]

theorem physicalPhaseAngleSlope_analyticAt_slit (q : ℂ × ℂ)
    (hq : isotropicDiscriminant q ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => physicalPhaseAngleSlope p.1 p.2) q := by
  have hd : AnalyticAt ℂ isotropicDiscriminant q :=
    analyticAt_const.sub ((analyticAt_fst.sub (Complex.analyticAt_cos.comp analyticAt_snd)).pow 2)
  have hr : AnalyticAt ℂ (fun p => Complex.sqrt (isotropicDiscriminant p)) q := by
    simpa only [Complex.sqrt] using hd.cpow (g := fun _ => (2⁻¹ : ℂ)) analyticAt_const hq
  have hn : Complex.sqrt (isotropicDiscriminant q) ≠ 0 := by
    intro hz
    have hh := sqrt_re_pos_of_slit hq
    simp only [hz, Complex.zero_re] at hh
    exact hh.false
  simp only [physicalPhaseAngleSlope, upperPhysicalPhase_sin]
  exact (Complex.analyticAt_sin.comp analyticAt_snd).neg.div hr hn

theorem physicalPhaseNegativeCurvature_analyticAt_slit (q : ℂ × ℂ)
    (hq : isotropicDiscriminant q ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => physicalPhaseNegativeCurvature p.1 p.2) q := by
  have hd : AnalyticAt ℂ isotropicDiscriminant q :=
    analyticAt_const.sub ((analyticAt_fst.sub (Complex.analyticAt_cos.comp analyticAt_snd)).pow 2)
  have hr : AnalyticAt ℂ (fun p => Complex.sqrt (isotropicDiscriminant p)) q := by
    simpa only [Complex.sqrt] using hd.cpow (g := fun _ => (2⁻¹ : ℂ)) analyticAt_const hq
  have hn : Complex.sqrt (isotropicDiscriminant q) ≠ 0 := by
    intro hz
    have hh := sqrt_re_pos_of_slit hq
    simp only [hz, Complex.zero_re] at hh
    exact hh.false
  simp only [physicalPhaseNegativeCurvature_sqrt]
  exact (analyticAt_fst.mul (analyticAt_const.sub ((Complex.analyticAt_cos.comp analyticAt_snd).mul
    (analyticAt_fst.sub (Complex.analyticAt_cos.comp analyticAt_snd))))).div (hr.pow 3) (pow_ne_zero _ hn)

end IsingBulk.AnisoF002.Isotropic
