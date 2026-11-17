import IsingBulk.AnisoF002.C03.IsotropicWholePositiveCurvature
import IsingBulk.AnisoF002.C03.IsotropicCurvatureIntegral

/-!
# Integrated actual fixed-population curvature

The pointwise positive frozen projection is integrated along the genuine
fixed-population phase slope. This gives the exact extreme-coordinate
denominator scale before restoring all occupancy derivatives.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric MeasureTheory IsingBulk.AnisoF002.RegularTail

theorem projected_slope_difference_integral (B K : ℝ → ℂ) (m M : ℝ) (hmM : m ≤ M)
    (hB : ∀ u ∈ Icc m M, HasDerivAt B (-K u) u)
    (hK : ContinuousOn K (Icc m M)) :
    (∫ u in m..M, (frozenObliqueRotation * K u).re) =
      (frozenObliqueRotation * (B m - B M)).re := by
  have hproj : ContinuousOn (fun u => (frozenObliqueRotation * K u).re) (Icc m M) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hK)
  have hint : IntervalIntegrable (fun u => (frozenObliqueRotation * K u).re) volume m M := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hmM] using hproj
  have hd (u : ℝ) (hu : u ∈ uIcc m M) :
      HasDerivAt (fun x => -(frozenObliqueRotation * B x).re)
        (frozenObliqueRotation * K u).re u := by
    rw [uIcc_of_le hmM] at hu
    have hh := ((hB u hu).const_mul frozenObliqueRotation).neg
    have hg := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hh
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.neg_re, mul_neg, neg_neg] using! hg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [hi, mul_sub, Complex.sub_re]
  ring

theorem fixedOccupancyPhaseCurvature_continuous (s : ℂ) (hs : 0 < s.im)
    (η τ ρ υ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hυ : 0 ≤ υ) :
    Continuous (fixedOccupancyPhaseCurvature s η τ ρ υ) := by
  have hmap : Continuous (fun θ : ℝ => ((s, τ, ρ, υ, θ) : FixedPhaseParameters)) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hq : isotropicDiscriminant (fixedPhasePoint η (s, τ, ρ, υ, θ)) ∈ Complex.slitPlane :=
    edge_discriminant_slit (Or.inl (fixedOccupancyAngle_sheet s hs η τ ρ υ θ hη hτ hρ hυ))
  have hh : ContinuousAt (fun u : ℝ => fixedPhaseCurvatureParameters η (s, τ, ρ, υ, u)) θ :=
    (fixedPhaseCurvatureParameters_continuousAt η _ hq).comp
      (f := fun u : ℝ => ((s, τ, ρ, υ, u) : FixedPhaseParameters)) hmap.continuousAt
  exact hh

/-- Frozen `eq:iso-fixed-occupancy-curvature` for the actual canonical
phase and full fixed populations, derived by integration on the entire
nonnegative right interval, including the enlarged upper endpoint. -/
theorem exists_fixedOccupancy_phase_slope_difference (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ m M : ℝ, 0 ≤ m → m ≤ M → M ≤ b + δ →
        c * positiveCurvatureScale m M (ε + τ * ρ) ≤
          (frozenObliqueRotation *
            (fixedOccupancyPhaseSlope (isotropicRadialParameter α ε) η τ ρ υ (-b + m) -
              fixedOccupancyPhaseSlope (isotropicRadialParameter α ε) η τ ρ υ (-b + M))).re := by
  obtain ⟨δ, c, hδ, hδ1, hc, hcurv⟩ :=
    exists_fixedOccupancy_positive_phase_curvature α b η hα hb hpoint hη hwidth
  refine ⟨δ, c, hδ, hδ1, hc, ?_⟩
  intro ε hε hεδ τ ρ υ hτ hρ hυ m M hm hmM hM
  let s := isotropicRadialParameter α ε
  let E := ε + τ * ρ
  let B : ℝ → ℂ := fun u => fixedOccupancyPhaseSlope s η τ ρ υ (-b + u)
  let K : ℝ → ℂ := fun u => fixedOccupancyPhaseCurvature s η τ ρ υ (-b + u)
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hE : 0 < E := add_pos_of_pos_of_nonneg hε (mul_nonneg hτ.1 hρ.1)
  have hB (u : ℝ) (_hu : u ∈ Icc m M) : HasDerivAt B (-K u) u := by
    have hbump : HasDerivAt (fun v : ℝ => -b + v) 1 u := by
      simpa only [id_eq] using (hasDerivAt_id u).const_add (-b)
    have hh := (fixedOccupancyPhaseSlope_hasDerivAt s hs η τ ρ υ (-b + u) hη hτ.1 hρ.1 hυ.1).scomp u hbump
    simpa only [B, K, Function.comp_def, id_eq, one_smul] using! hh
  have hK : Continuous K := (fixedOccupancyPhaseCurvature_continuous s hs η τ ρ υ hη hτ.1 hρ.1 hυ.1).comp
    (continuous_const.add continuous_id)
  have hproj : Continuous (fun u => (frozenObliqueRotation * K u).re) :=
    Complex.continuous_re.comp (continuous_const.mul hK)
  have hweight : IntervalIntegrable (fun u => c * positiveCurvatureWeight E u) volume m M := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hmM]
    exact continuousOn_const.mul (positiveCurvatureWeight_continuousOn hm hE)
  have hmono := intervalIntegral.integral_mono_on hmM hweight (hproj.intervalIntegrable m M)
    (show ∀ u ∈ Icc m M, c * positiveCurvatureWeight E u ≤ (frozenObliqueRotation * K u).re by
      intro u hu
      have hθ : -b + u ∈ Icc (-b) δ := ⟨by linarith only [hm, hu.1], by linarith only [hM, hu.2]⟩
      have hh := hcurv ε hε hεδ τ ρ υ hτ hρ hυ (-b + u) hθ
      simpa only [positiveCurvatureWeight, E, K, s, show -b + u + b = u by ring, add_assoc, ← mul_div_assoc, mul_one] using hh)
  rw [intervalIntegral.integral_const_mul, positiveCurvatureScale_integral hm hmM hE,
    projected_slope_difference_integral B K m M hmM hB hK.continuousOn] at hmono
  exact hmono

end IsingBulk.AnisoF002.Isotropic
