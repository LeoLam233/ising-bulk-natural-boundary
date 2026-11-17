import IsingBulk.AnisoF002.C03.IsotropicBranchSector

/-!
# The actual complex curvature numerator near the lower branch

The positive limiting numerator is computed from the exact dispersion.
Continuity gives a common relative-error neighborhood on the actual
radial parameter and outward contour, before every population choice.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

def phaseCurvatureNumerator (q : ℂ × ℂ) : ℂ :=
  q.1 * (1 - Complex.cos q.2 * (q.1 - Complex.cos q.2))

theorem phaseCurvatureNumerator_continuous : Continuous phaseCurvatureNumerator := by
  unfold phaseCurvatureNumerator
  fun_prop

def branchCurvatureNumerator (b : ℝ) : ℝ :=
  (1 + Real.cos b) * (1 - Real.cos b)

theorem branchCurvatureNumerator_pos (b : ℝ) (hb : 0 < b ∧ b < Real.pi) :
    0 < branchCurvatureNumerator b := by
  have hlow := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hlow
  have hhigh := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) hb.2.le hb.1
  rw [Real.cos_zero] at hhigh
  unfold branchCurvatureNumerator
  exact mul_pos (by linarith only [hlow]) (by linarith only [hhigh])

theorem phaseCurvatureNumerator_at_branch (b : ℝ) :
    phaseCurvatureNumerator (((1 + Real.cos b : ℝ) : ℂ), ((-b : ℝ) : ℂ)) =
      (branchCurvatureNumerator b : ℂ) := by
  simp only [phaseCurvatureNumerator, Complex.ofReal_neg, Complex.cos_neg,
    ← Complex.ofReal_cos, branchCurvatureNumerator]
  push_cast
  ring

theorem exists_isotropic_branch_curvature_numerator_near (α b γ : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hγ : 0 < γ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ u h : ℝ, |u| ≤ r → |h| ≤ r →
        ‖phaseCurvatureNumerator (isotropicRadialParameter α ε,
            ((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)) -
              (branchCurvatureNumerator b : ℂ)‖ ≤ γ := by
  let q₀ : ℂ × ℂ := (((1 + Real.cos b : ℝ) : ℂ), ((-b : ℝ) : ℂ))
  have hcont : ContinuousAt phaseCurvatureNumerator q₀ := phaseCurvatureNumerator_continuous.continuousAt
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hcont γ hγ
  let r := min 1 (δ / 8)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : r ≤ δ / 8 := min_le_right _ _
  refine ⟨r, hr, hr1, ?_⟩
  intro ε hε hεr u h hu hh
  have hs := (isotropicRadialParameter_estimates α ε hα hε (hεr.trans hr1)).2.2.2.2
  have hsδ : dist (isotropicRadialParameter α ε) (((1 + Real.cos b : ℝ) : ℂ)) < δ := by
    rw [hpoint]
    exact hs.trans_lt (by linarith only [hεr, hrδ, hδ])
  have hw : dist (((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)) ((-b : ℝ) : ℂ) < δ := by
    rw [dist_eq_norm]
    have he : (((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)) - ((-b : ℝ) : ℂ) =
        (u : ℂ) - Complex.I * (h : ℂ) := by push_cast; ring
    rw [he]
    have hbnd : ‖(u : ℂ) - Complex.I * (h : ℂ)‖ ≤ |u| + |h| := by
      simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_sub_le (u : ℂ) (Complex.I * (h : ℂ))
    exact hbnd.trans_lt (by linarith only [hu, hh, hrδ, hδ])
  have hd : dist (isotropicRadialParameter α ε,
      ((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)) q₀ < δ := by
    simpa only [q₀, Prod.dist_eq, max_lt_iff] using And.intro hsδ hw
  have ht := hnear hd
  rw [phaseCurvatureNumerator_at_branch, dist_eq_norm] at ht
  exact ht.le

end IsingBulk.AnisoF002.Isotropic
