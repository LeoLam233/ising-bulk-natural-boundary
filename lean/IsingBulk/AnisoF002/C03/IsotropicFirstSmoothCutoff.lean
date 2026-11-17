import IsingBulk.AnisoF002.C03.IsotropicCollisionCoefficientSplit
import IsingBulk.AnisoF002.C03.IsotropicFirstSmallCharts

/-!
# The actual smooth first-chart cutoff on the original shape space

This is the same near-coincidence cutoff used in the full physical
coefficient partition.  Its scaled value tends to one, while its complete
transition annulus stays under the original full-density majorant.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators ContDiff

def isotropicFirstShapeCutoff {n : ℕ} (r : ℝ) (q : Fin n → ℝ) : ℂ :=
  (collisionNearCutoff r (centeredConstraintAngles 0 q) : ℂ)

theorem isotropicFirstShapeCutoff_centered {n : ℕ} (r μ : ℝ) (q : Fin n → ℝ) :
    (collisionNearCutoff r (centeredConstraintAngles μ q) : ℂ) = isotropicFirstShapeCutoff r q := by
  simp only [isotropicFirstShapeCutoff, collisionNearCutoff, collisionAwayCutoff,
    angularCenteredQuadratic_centered]

theorem isotropicFirstShapeCutoff_continuous (n : ℕ) (r : ℝ) :
    Continuous (isotropicFirstShapeCutoff (n := n) r) :=
  Complex.continuous_ofReal.comp ((collisionNearCutoff_contDiff (n + 1) r).continuous.comp
    (centeredConstraintAngles_continuous 0))

theorem isotropicFirstShapeCutoff_norm_le_one {n : ℕ} (r : ℝ) (q : Fin n → ℝ) :
    ‖isotropicFirstShapeCutoff r q‖ ≤ 1 := by
  have hh := (collisionCutoff_bounds r (centeredConstraintAngles 0 q)).2
  simpa only [isotropicFirstShapeCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hh.1] using hh.2

theorem isotropicFirstShapeCutoff_one {n : ℕ} {r : ℝ} (hr : 0 < r) (q : Fin n → ℝ)
    (hq : angularQuadratic (flatConstrainedAngles q) ≤ r) : isotropicFirstShapeCutoff r q = 1 := by
  have hh := collisionNearCutoff_one hr (centeredConstraintAngles 0 q)
    (by simpa only [angularCenteredQuadratic_centered] using hq)
  simp only [isotropicFirstShapeCutoff, hh, Complex.ofReal_one]

theorem isotropicFirstShapeCutoff_zero {n : ℕ} {r : ℝ} (hr : 0 < r) (q : Fin n → ℝ)
    (hq : 2 * r ≤ angularQuadratic (flatConstrainedAngles q)) : isotropicFirstShapeCutoff r q = 0 := by
  have hh := collisionNearCutoff_zero hr (centeredConstraintAngles 0 q)
    (by simpa only [angularCenteredQuadratic_centered] using hq)
  simp only [isotropicFirstShapeCutoff, hh, Complex.ofReal_zero]

theorem isotropicFirstShapeCutoff_support {n : ℕ} {r : ℝ} (hr : 0 < r) (q : Fin n → ℝ)
    (hq : isotropicFirstShapeCutoff r q ≠ 0) : angularQuadratic (flatConstrainedAngles q) < 2 * r := by
  by_contra hh
  exact hq (isotropicFirstShapeCutoff_zero hr q (le_of_not_gt hh))

theorem isotropicFirstShapeCutoff_at_zero {n : ℕ} {r : ℝ} (hr : 0 < r) :
    isotropicFirstShapeCutoff r (0 : Fin n → ℝ) = 1 := by
  apply isotropicFirstShapeCutoff_one hr
  have hz : flatConstrainedAngles (0 : Fin n → ℝ) = fun _ => 0 := by
    funext i
    induction i using Fin.lastCases <;> simp [flatConstrainedAngles]
  simpa only [hz, angularQuadratic, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero] using hr.le

def isotropicFirstScaledSmooth {n : ℕ} (α : ℝ) (σ : ℂ) (j : ℕ) (r s : ℝ)
    (q : Fin n → ℝ) : ℂ :=
  isotropicFirstShapeCutoff r (s • q) * isotropicFirstRealScaledJet α σ j s (flatConstrainedAngles q)

theorem isotropicFirstScaledSmooth_continuous {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (j : ℕ) (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Continuous (isotropicFirstScaledSmooth (n := n) α σ j r s) :=
  ((isotropicFirstShapeCutoff_continuous n r).comp (by fun_prop)).mul
    ((isotropicFirstRealScaledJet_continuous (Nat.succ_pos n) hα hπ σ hσ j hs).comp
      (flatConstrainedAngles_continuous n))

theorem isotropicFirstScaledSmooth_limit {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    {r : ℝ} (hr : 0 < r) (q : Fin n → ℝ) (j : ℕ) :
    Tendsto (fun s : ℝ => isotropicFirstScaledSmooth α σ j r s q) (𝓝[>] (0 : ℝ))
      (𝓝 (isotropicFirstLeadingJet α j (flatConstrainedAngles q))) := by
  have hc : ContinuousAt (fun s : ℝ => isotropicFirstShapeCutoff r (s • q)) 0 :=
    ((isotropicFirstShapeCutoff_continuous n r).comp (by fun_prop)).continuousAt
  have hlim : Tendsto (fun s : ℝ => isotropicFirstShapeCutoff r (s • q)) (𝓝[>] (0 : ℝ))
      (𝓝 (isotropicFirstShapeCutoff r ((0 : ℝ) • q))) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have hf := isotropicFirstRealScaledJet_limit (Nat.succ_pos n) hα hπ σ hres
    (flatConstrainedAngles q) (isotropic_flatConstrainedAngles_sum n q) j
  simpa only [isotropicFirstScaledSmooth, zero_smul, isotropicFirstShapeCutoff_at_zero hr, one_mul]
    using hlim.mul hf

end
end IsingBulk.AnisoF002.Isotropic
