import IsingBulk.AnisoF002.C03.IsotropicBranchNumerator
import IsingBulk.AnisoF002.C03.IsotropicFrozenProjection

/-!
# Positive frozen projection of the actual branch curvature

The actual second angular derivative has the required inverse-cubic
square-root size and a strictly positive 3 pi / 8 projection, uniformly
for the whole nonnegative branch window and all outward depths.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem exists_isotropic_positive_branch_curvature (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ r c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ u h : ℝ,
        u ∈ Icc 0 r → h ∈ Icc 0 r →
        c / Real.sqrt (u + ε + h) ^ 3 ≤
          (frozenObliqueRotation * physicalPhaseNegativeCurvature (isotropicRadialParameter α ε)
            (((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ))).re := by
  let n := branchCurvatureNumerator b
  have hn : 0 < n := branchCurvatureNumerator_pos b hb
  have ha := frozenObliqueAngle_cos_pos
  obtain ⟨rS, hrS, _, hsector⟩ := exists_isotropic_positive_branch_sine_sector α b hα hb hpoint
  obtain ⟨rB, _, C, hrB, hrB1, _, hC, hsine⟩ :=
    exists_isotropic_branch_sine_bounds α b hα hb hpoint
  obtain ⟨rN, hrN, _, hnum⟩ := exists_isotropic_branch_curvature_numerator_near α b
    (n * Real.cos frozenObliqueAngle / 54) hα hpoint (by positivity)
  let r := min rS (min rB rN)
  let c := n * Real.cos frozenObliqueAngle / (54 * C ^ 3)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrS' : r ≤ rS := min_le_left _ _
  have hrB' : r ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hrN' : r ≤ rN := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, c, hr, hrB'.trans hrB1, by dsimp [c]; positivity, ?_⟩
  intro ε hε hεr u h hu hh
  let w : ℂ := ((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)
  let s := isotropicRadialParameter α ε
  let z := Complex.sin (upperPhysicalPhase (isotropicBranchDispersion α b ε u h))
  let q := phaseCurvatureNumerator (s, w)
  have hsector' := hsector ε hε (hεr.trans hrS') u h
    ⟨hu.1, hu.2.trans hrS'⟩ ⟨hh.1, hh.2.trans hrS'⟩
  have hnum' : ‖q - (n : ℂ)‖ ≤ n * Real.cos frozenObliqueAngle / 54 :=
    hnum ε hε (hεr.trans hrN') u h
      (by rw [abs_of_nonneg hu.1]; exact hu.2.trans hrN')
      (by rw [abs_of_nonneg hh.1]; exact hh.2.trans hrN')
  have hproj := frozen_projection_curvature_perturbation z q n
    hsector'.1 hsector'.2.1.le hsector'.2.2 hn hnum'
  have hupper := (hsine ε hε (hεr.trans hrB') u h
    (by rw [abs_of_nonneg hu.1]; exact hu.2.trans hrB')
    ⟨hh.1, hh.2.trans hrB'⟩).2
  rw [abs_of_nonneg hu.1] at hupper
  change ‖z‖ ≤ C * Real.sqrt (u + ε + h) at hupper
  have hz : z ≠ 0 := by
    intro he
    have hre := hsector'.1
    change 0 < z.re at hre
    simp only [he, Complex.zero_re] at hre
    exact hre.false
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hT : 0 < u + ε + h := by linarith only [hu.1, hε, hh.1]
  have hsT : 0 < Real.sqrt (u + ε + h) := Real.sqrt_pos.mpr hT
  have he : physicalPhaseNegativeCurvature s w = q / z ^ 3 := by
    simp only [physicalPhaseNegativeCurvature, q, phaseCurvatureNumerator,
      upperPhysicalPhase_cos, isotropicDispersion, z, isotropicBranchDispersion, s, w]
  change c / Real.sqrt (u + ε + h) ^ 3 ≤ (frozenObliqueRotation * physicalPhaseNegativeCurvature s w).re
  rw [he]
  calc
    _ = n * Real.cos frozenObliqueAngle / (54 * (C * Real.sqrt (u + ε + h)) ^ 3) := by
      dsimp [c]
      ring
    _ ≤ n * Real.cos frozenObliqueAngle / (54 * ‖z‖ ^ 3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hupper 3) (by norm_num)
    _ ≤ _ := hproj

end IsingBulk.AnisoF002.Isotropic
