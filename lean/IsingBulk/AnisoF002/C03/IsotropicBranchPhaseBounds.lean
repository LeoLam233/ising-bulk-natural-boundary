import IsingBulk.AnisoF002.C03.IsotropicBranchCoercivity

/-!
# Two-sided square-root bounds for the actual branch phase

The exact physical phase satisfies sin(phi)^2=(1-W)(1+W).
The branch discriminant bounds therefore give the true square-root
size of sin(phi), uniformly for outward displacement and the physical
radial parameter. No square-root model replaces the phase.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem upperPhysicalPhase_sine_norm_sq (W : ℂ) :
    ‖Complex.sin (upperPhysicalPhase W)‖ ^ 2 = ‖1 - W‖ * ‖1 + W‖ := by
  rw [← norm_pow, Complex.sin_sq, upperPhysicalPhase_cos]
  rw [show (1 : ℂ) - W ^ 2 = (1 - W) * (1 + W) by ring, norm_mul]

theorem one_add_norm_of_near_one (W : ℂ) (hW : ‖1 - W‖ ≤ 1) :
    1 ≤ ‖1 + W‖ ∧ ‖1 + W‖ ≤ 3 := by
  have hlow := norm_add_le (1 + W) (1 - W)
  rw [show (1 + W) + (1 - W) = (2 : ℂ) by ring, Complex.norm_two] at hlow
  have hupp := norm_sub_le (2 : ℂ) (1 - W)
  rw [show (2 : ℂ) - (1 - W) = 1 + W by ring, Complex.norm_two] at hupp
  constructor <;> linarith

/-- Both constants and the full common branch neighborhood are chosen
before every angular population. The estimate includes the negative
branch segment and the branch point itself for every epsilon>0. -/
theorem exists_isotropic_branch_sine_bounds (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ r c C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ u h : ℝ, |u| ≤ r → h ∈ Icc 0 r →
        c * Real.sqrt (|u| + ε + h) ≤
            ‖Complex.sin (upperPhysicalPhase (isotropicBranchDispersion α b ε u h))‖ ∧
        ‖Complex.sin (upperPhysicalPhase (isotropicBranchDispersion α b ε u h))‖ ≤
            C * Real.sqrt (|u| + ε + h) := by
  obtain ⟨r₀, c₀, C₀, hr₀, hr₀1, hc₀, hC₀, hbounds⟩ :=
    exists_isotropic_branch_coercivity α b hα hb hpoint
  let r := min r₀ (1 / (3 * C₀))
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hr0 : r ≤ r₀ := min_le_left _ _
  have hrC : 3 * C₀ * r ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 3 * C₀)).mp (min_le_right r₀ (1 / (3 * C₀)))
    nlinarith only [h]
  refine ⟨r, Real.sqrt c₀, Real.sqrt (3 * C₀), hr, hr0.trans hr₀1,
    Real.sqrt_pos.mpr hc₀, Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro ε hε hεr u h hu hh
  let W := isotropicBranchDispersion α b ε u h
  let T := |u| + ε + h
  have hT : 0 < T := by dsimp [T]; linarith [abs_nonneg u, hh.1]
  obtain ⟨hlo, hhi⟩ := hbounds ε hε (hεr.trans hr0) u h (hu.trans hr0)
    ⟨hh.1, hh.2.trans hr0⟩
  have hnear : ‖1 - W‖ ≤ 1 := by
    change ‖1 - isotropicBranchDispersion α b ε u h‖ ≤ 1
    have hTmax : |u| + ε + h ≤ 3 * r := by linarith only [hu, hεr, hh.2]
    exact hhi.trans ((mul_le_mul_of_nonneg_left hTmax hC₀.le).trans (by nlinarith only [hrC]))
  obtain ⟨hpluslo, hplushi⟩ := one_add_norm_of_near_one W hnear
  have hsine := upperPhysicalPhase_sine_norm_sq W
  have hsqlo : c₀ * T ≤ ‖Complex.sin (upperPhysicalPhase W)‖ ^ 2 := by
    have hn := mul_le_mul_of_nonneg_left hpluslo (norm_nonneg (1 - W))
    rw [mul_one] at hn
    rw [hsine]
    exact hlo.trans hn
  have hsqhi : ‖Complex.sin (upperPhysicalPhase W)‖ ^ 2 ≤ 3 * C₀ * T := by
    rw [hsine]
    exact (mul_le_mul hhi hplushi (norm_nonneg _) (by positivity)).trans_eq (by ring)
  constructor
  · have h := (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hsqlo⟩
    rwa [Real.sqrt_mul hc₀.le] at h
  · have h := Real.le_sqrt_of_sq_le hsqhi
    rwa [Real.sqrt_mul (by positivity : 0 ≤ 3 * C₀)] at h

end IsingBulk.AnisoF002.Isotropic
