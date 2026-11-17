import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferCurvature
import IsingBulk.AnisoF002.C03.IsotropicIntegratedCurvature

/-!
# The actual integrated fixed-population curvature on a preselected angular arc
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric Filter MeasureTheory

theorem exists_fixedOccupancy_phase_slope_difference_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ c : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ m M : ℝ, 0 ≤ m → m ≤ M → M ≤ b + β →
        c * positiveCurvatureScale m M (ε + τ * ρ) ≤
          (frozenObliqueRotation *
            (fixedOccupancyPhaseSlope (isotropicRadialParameter α ε) η τ ρ υ (-b + m) -
              fixedOccupancyPhaseSlope (isotropicRadialParameter α ε) η τ ρ υ (-b + M))).re := by
  obtain ⟨β, hβ, hβ1, hdata⟩ :=
    exists_fixedOccupancy_positive_curvature_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, c, hδ, hδβ, hc, hcurv⟩ := hdata η hη hwidth
  have hδ1 := hδβ.trans hβ1
  refine ⟨δ, c, hδ, hδβ, hc, ?_⟩
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
      have hθ : -b + u ∈ Icc (-b) β := ⟨by linarith only [hm, hu.1], by linarith only [hM, hu.2]⟩
      have hh := hcurv ε hε hεδ τ ρ υ hτ hρ hυ (-b + u) hθ
      simpa only [positiveCurvatureWeight, E, K, s, show -b + u + b = u by ring, add_assoc, ← mul_div_assoc, mul_one] using hh)
  rw [intervalIntegral.integral_const_mul, positiveCurvatureScale_integral hm hmM hE,
    projected_slope_difference_integral B K m M hmM hB hK.continuousOn] at hmono
  exact hmono

end IsingBulk.AnisoF002.Isotropic
