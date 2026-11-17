import IsingBulk.AnisoF002.C03.IsotropicFixedPhaseCurvature

/-!
# A common compact neighborhood for the full fixed-population curvature

The compact set includes both complete population fractions. The exact
fixed-population phase curvature is continuous on its genuine regular
discriminant domain, including the limiting real right interval away
from its branch point.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric Filter

abbrev FixedPhaseParameters := ℂ × (ℝ × (ℝ × (ℝ × ℝ)))

def fixedPhasePoint (η : ℝ) (q : FixedPhaseParameters) : ℂ × ℂ :=
  (q.1, fixedOccupancyAngle η q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)

def fixedPhaseCurvatureParameters (η : ℝ) (q : FixedPhaseParameters) : ℂ :=
  fixedOccupancyPhaseCurvature q.1 η q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

theorem fixedPhasePoint_continuous (η : ℝ) : Continuous (fixedPhasePoint η) := by
  have hp : Continuous (upperPeriodicBump η) := (upperPeriodicBump_contDiff η (n := 0)).continuous
  have hm : Continuous (lowerPeriodicBump η) := (lowerPeriodicBump_contDiff η (n := 0)).continuous
  unfold fixedPhasePoint fixedOccupancyAngle
  fun_prop

theorem fixedPhaseSlope_continuous (η : ℝ) :
    Continuous (fun q : FixedPhaseParameters => fixedOccupancySlope η q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hp : Continuous (deriv (upperPeriodicBump η)) :=
    (show ContDiff ℝ 1 (deriv (upperPeriodicBump η)) from
      (upperPeriodicBump_contDiff η (n := 2)).deriv').continuous
  have hm : Continuous (deriv (lowerPeriodicBump η)) :=
    (show ContDiff ℝ 1 (deriv (lowerPeriodicBump η)) from
      (lowerPeriodicBump_contDiff η (n := 2)).deriv').continuous
  unfold fixedOccupancySlope
  fun_prop

theorem fixedPhaseSecondSlope_continuous (η : ℝ) :
    Continuous (fun q : FixedPhaseParameters => fixedOccupancySecondSlope η q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hp : Continuous (deriv (deriv (upperPeriodicBump η))) :=
    (show ContDiff ℝ 1 (deriv (deriv (upperPeriodicBump η))) from
      (upperPeriodicBump_contDiff η (n := 3)).deriv'.deriv').continuous
  have hm : Continuous (deriv (deriv (lowerPeriodicBump η))) :=
    (show ContDiff ℝ 1 (deriv (deriv (lowerPeriodicBump η))) from
      (lowerPeriodicBump_contDiff η (n := 3)).deriv'.deriv').continuous
  unfold fixedOccupancySecondSlope
  fun_prop

theorem fixedPhaseCurvatureParameters_continuousAt (η : ℝ) (q : FixedPhaseParameters)
    (hq : isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane) :
    ContinuousAt (fixedPhaseCurvatureParameters η) q := by
  have hc := (physicalPhaseNegativeCurvature_analyticAt_slit _ hq).continuousAt.comp
    (fixedPhasePoint_continuous η).continuousAt
  have hs := (physicalPhaseAngleSlope_analyticAt_slit _ hq).continuousAt.comp
    (fixedPhasePoint_continuous η).continuousAt
  exact (hc.mul ((fixedPhaseSlope_continuous η).continuousAt.pow 2)).sub
    (hs.mul (fixedPhaseSecondSlope_continuous η).continuousAt)

theorem physical_positive_right_curvature (S b θ : ℝ)
    (hS : 0 < S) (hb : 0 < b ∧ b < Real.pi) (hpoint : 1 + Real.cos b = S)
    (hθ : -b < θ ∧ θ ≤ 0) :
    isotropicDiscriminant ((S : ℂ), (θ : ℂ)) ∈ Complex.slitPlane ∧
      0 < (frozenObliqueRotation * physicalPhaseNegativeCurvature (S : ℂ) (θ : ℂ)).re := by
  let W := S - Real.cos θ
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (neg_nonneg.mpr hθ.2) hb.2.le
    (by linarith only [hθ.1])
  rw [Real.cos_neg] at hcos
  have hWlo : -1 < W := by dsimp [W]; linarith only [hS, Real.cos_le_one θ]
  have hWhi : W < 1 := by dsimp [W]; linarith only [hcos, hpoint]
  have hWabs : |W| < 1 := abs_lt.mpr ⟨hWlo, hWhi⟩
  have hD : 0 < 1 - W ^ 2 := by nlinarith only [(sq_lt_one_iff_abs_lt_one W).mpr hWabs]
  have hdeq : isotropicDiscriminant ((S : ℂ), (θ : ℂ)) = ((1 - W ^ 2 : ℝ) : ℂ) := by
    simp only [isotropicDiscriminant, isotropicDispersion, ← Complex.ofReal_cos, W]
    push_cast
    rfl
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa only [hdeq, Complex.ofReal_re] using hD)), ?_⟩
  have hprod : Real.cos θ * W < 1 := by
    apply (le_abs_self _).trans_lt
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (abs_nonneg W)).trans_eq (one_mul _)).trans_lt hWabs
  let F := S * (1 - Real.cos θ * W) / Real.sqrt (1 - W ^ 2) ^ 3
  have hF : 0 < F := by dsimp [F]; positivity
  have hvalue : physicalPhaseNegativeCurvature (S : ℂ) (θ : ℂ) = (F : ℂ) := by
    rw [physicalPhaseNegativeCurvature_sqrt, ← Complex.ofReal_cos]
    have hdeq' : (1 : ℂ) - ((S : ℂ) - (Real.cos θ : ℂ)) ^ 2 = ((1 - W ^ 2 : ℝ) : ℂ) := by
      dsimp [W]
      push_cast
      rfl
    rw [hdeq', Complex.sqrt_of_nonneg (by exact_mod_cast hD.le), Complex.ofReal_re]
    dsimp [F, W]
    push_cast
    rfl
  rw [hvalue, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    frozenObliqueRotation_eq]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  exact mul_pos frozenObliqueAngle_cos_pos hF

def fixedPhaseRegularCompact (S b R : ℝ) : Set FixedPhaseParameters :=
  {((S : ℂ))} ×ˢ ({(0 : ℝ)} ×ˢ (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc (-b + R / 2) 0)))

theorem fixedPhaseRegularCompact_isCompact (S b R : ℝ) :
    IsCompact (fixedPhaseRegularCompact S b R) :=
  isCompact_singleton.prod (isCompact_singleton.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)))

theorem fixedPhase_zero_values (η : ℝ) (S : ℂ) (ρ υ θ : ℝ) :
    fixedPhasePoint η (S, 0, ρ, υ, θ) = (S, (θ : ℂ)) ∧
      fixedPhaseCurvatureParameters η (S, 0, ρ, υ, θ) = physicalPhaseNegativeCurvature S (θ : ℂ) := by
  simp only [fixedPhasePoint, fixedOccupancyAngle, fixedPhaseCurvatureParameters,
    fixedOccupancyPhaseCurvature, fixedOccupancySlope, fixedOccupancySecondSlope,
    zero_mul, Complex.ofReal_zero, mul_zero, sub_zero, one_pow, mul_one]
  trivial

/-- A single compact neighborhood includes every complete population
fraction and the full smooth bump transition region away from the branch. -/
theorem exists_fixedPhase_regular_curvature_tube (S b R η : ℝ)
    (hS : 0 < S) (hb : 0 < b ∧ b < Real.pi) (hpoint : 1 + Real.cos b = S)
    (hR : 0 < R) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ q ∈ cthickening δ (fixedPhaseRegularCompact S b R),
        isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane ∧
          c ≤ (frozenObliqueRotation * fixedPhaseCurvatureParameters η q).re := by
  let K := fixedPhaseRegularCompact S b R
  let H : FixedPhaseParameters → ℝ := fun q => (frozenObliqueRotation * fixedPhaseCurvatureParameters η q).re
  have hK := fixedPhaseRegularCompact_isCompact S b R
  have hregular : ∀ q ∈ K, isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane ∧ 0 < H q := by
    rintro ⟨s, τ, ρ, υ, θ⟩ ⟨hs, hτ, _, _, hθ⟩
    have hs' : s = (S : ℂ) := hs
    have hτ' : τ = 0 := hτ
    subst s τ
    have hh := physical_positive_right_curvature S b θ hS hb hpoint
      ⟨by linarith only [hθ.1, hR], hθ.2⟩
    simpa only [H, (fixedPhase_zero_values η (S : ℂ) ρ υ θ).1,
      (fixedPhase_zero_values η (S : ℂ) ρ υ θ).2] using hh
  have hHcont (q : FixedPhaseParameters) (hq : isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane) :
      ContinuousAt H q :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_const.mul (fixedPhaseCurvatureParameters_continuousAt η q hq))
  obtain ⟨c, hc, hclower⟩ := hK.exists_forall_le'
    (fun q hq => (hHcont q (hregular q hq).1).continuousWithinAt) (fun q hq => (hregular q hq).2)
  let O : Set FixedPhaseParameters := {q | isotropicDiscriminant (fixedPhasePoint η q) ∈ Complex.slitPlane ∧ c / 2 < H q}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hd := (isotropicDiscriminant_continuous.comp (fixedPhasePoint_continuous η)).continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds hq.1)
    have hp := (hHcont q hq.1).eventually (lt_mem_nhds hq.2)
    filter_upwards [hd, hp] with p hdp hpp
    exact ⟨hdp, hpp⟩
  have hsub : K ⊆ O := by
    intro q hq
    exact ⟨(hregular q hq).1, lt_of_lt_of_le (by linarith only [hc]) (hclower q hq)⟩
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_cthickening_subset_open hO hsub
  refine ⟨δ, c / 2, hδ, by linarith only [hc], ?_⟩
  intro q hq
  exact ⟨(hδsub hq).1, (hδsub hq).2.le⟩

end IsingBulk.AnisoF002.Isotropic
