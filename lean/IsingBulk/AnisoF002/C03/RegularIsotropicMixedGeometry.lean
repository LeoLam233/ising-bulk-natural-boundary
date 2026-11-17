import IsingBulk.AnisoF002.C03.RegularIsotropicMixedGap
import IsingBulk.AnisoF002.C03.RegularIsotropicPairGap
import IsingBulk.AnisoF002.C03.RegularIsotropicBranchWeights

/-!
# Uniform geometry of the actual mixed contour

Cosine bands select the two true branches periodically, before the
particle number. Every selected coordinate contributes one to the
actual raw bump population. The genuine balanced displacement controls
the spectral argument uniformly over the entire angular circle.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators Classical
open IsingBulk.AnisoF002.RegularTail

theorem complex_cos_vertical_difference (θ h : ℝ) (hh : |h| ≤ 1) :
    ‖Complex.cos ((θ : ℂ) - Complex.I * (h : ℂ)) - (Real.cos θ : ℂ)‖ ≤ 2 * |h| := by
  have he : Complex.cos ((θ : ℂ) - Complex.I * (h : ℂ)) - (Real.cos θ : ℂ) =
      ((Real.cos θ * (Real.cosh h - 1) : ℝ) : ℂ) +
        Complex.I * ((Real.sin θ * Real.sinh h : ℝ) : ℂ) := by
    have hw : (θ : ℂ) - Complex.I * (h : ℂ) =
        (θ : ℂ) + ((-h : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hw, Complex.cos_add_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, Real.cosh_neg, Real.sinh_neg]
    push_cast
    ring
  have hc0 : 0 ≤ Real.cosh h - 1 := sub_nonneg.mpr (Real.one_le_cosh h)
  have hcos := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) hc0
  have hsin := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (abs_nonneg (Real.sinh h))
  have hex := Real.abs_exp_sub_one_le (x := |h|) (by simpa only [abs_abs] using hh)
  have hsum : Real.cosh h - 1 + |Real.sinh h| = Real.exp |h| - 1 := by
    rw [Real.abs_sinh, ← Real.cosh_abs h]
    linarith only [Real.cosh_add_sinh |h|]
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc0]
  have hnorm : Real.cosh h - 1 + |Real.sinh h| ≤ 2 * |h| := by
    rw [hsum]
    exact (le_abs_self _).trans (by simpa only [abs_abs] using hex)
  linarith

theorem actual_balanced_dispersion_perturbation {N : ℕ} (hN : 0 < N)
    (α ε η τ : ℝ) (hα : 0 < α ∧ α < Real.pi) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ) (i : Fin N) :
    ‖isotropicDispersion (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) -
      ((2 * Real.cos α - Real.cos (θ i) : ℝ) : ℂ)‖ ≤ 4 * ε + 2 * τ := by
  let h := balancedShift (τ / N) (fun j => upperPeriodicBump η (θ j))
    (fun j => lowerPeriodicBump η (θ j)) i
  have hh : |h| ≤ τ := by
    simpa only [h, Fintype.card_fin] using balancedShift_abs_le τ hτ.1
      (fun j => upperPeriodicBump η (θ j)) (fun j => lowerPeriodicBump η (θ j))
      (by simpa only [Fintype.card_fin] using hN)
      (fun j => upperPeriodicBump_bounds η (θ j)) (fun j => lowerPeriodicBump_bounds η (θ j)) i
  have hw : actualHomotopyAngle η τ 1 θ i = (θ i : ℂ) - Complex.I * (h : ℂ) := by
    simp only [actualHomotopyAngle, balancedHomotopyCoordinate, contourCoordinate,
      one_mul, Fintype.card_fin, h]
  have hrad := (isotropicRadialParameter_estimates α ε hα hε hε1).2.2.2.2
  rw [dist_eq_norm] at hrad
  have hcos := complex_cos_vertical_difference (θ i) h (hh.trans hτ.2)
  have he : isotropicDispersion (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) -
      ((2 * Real.cos α - Real.cos (θ i) : ℝ) : ℂ) =
      (isotropicRadialParameter α ε - ((2 * Real.cos α : ℝ) : ℂ)) -
        (Complex.cos ((θ i : ℂ) - Complex.I * (h : ℂ)) - (Real.cos (θ i) : ℂ)) := by
    rw [hw]
    dsimp [isotropicDispersion]
    push_cast
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

theorem cosine_band_sine_lower (b θ β : ℝ) (hb : 0 < Real.sin b)
    (hβ : β ≤ (Real.sin b) ^ 2 / 8) (hθ : |Real.cos θ - Real.cos b| ≤ β) :
    Real.sin b / 2 ≤ |Real.sin θ| := by
  have hsum : |Real.cos θ + Real.cos b| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_cos_le_one θ, Real.abs_cos_le_one b])
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans hθ
  have hp := mul_le_mul hθ hsum (abs_nonneg _) hβ0
  have he : |(Real.cos θ) ^ 2 - (Real.cos b) ^ 2| ≤ 2 * β := by
    rw [show (Real.cos θ) ^ 2 - (Real.cos b) ^ 2 =
      (Real.cos θ - Real.cos b) * (Real.cos θ + Real.cos b) by ring, abs_mul]
    nlinarith
  have hsqθ := Real.sin_sq_add_cos_sq θ
  have hsqb := Real.sin_sq_add_cos_sq b
  nlinarith [(abs_le.mp he).2, sq_abs (Real.sin θ), abs_nonneg (Real.sin θ)]

theorem cosine_band_bump_plateau (b η θ β : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hβ : β ≤ (Real.sin b) ^ 2 / 8)
    (hθ : |Real.cos θ - Real.cos b| ≤ β) :
    (upperPeriodicBump η θ = 1 ∧ lowerPeriodicBump η θ = 0) ∨
      (upperPeriodicBump η θ = 0 ∧ lowerPeriodicBump η θ = 1) := by
  have hb : 0 < Real.sin b := by linarith
  have hs := cosine_band_sine_lower b θ β hb hβ hθ
  by_cases hsin : 0 ≤ Real.sin θ
  · rw [abs_of_nonneg hsin] at hs
    left
    refine ⟨upperPeriodicBump_one hη (by linarith), ?_⟩
    apply upperPeriodicBump_zero hη
    rw [Real.sin_neg]
    linarith
  · rw [abs_of_neg (lt_of_not_ge hsin)] at hs
    right
    refine ⟨upperPeriodicBump_zero hη (by linarith), ?_⟩
    apply upperPeriodicBump_one hη
    rw [Real.sin_neg]
    linarith

def mixedCosBranchCoordinates {N : ℕ} (b β : ℝ) (θ : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => |Real.cos (θ i) - Real.cos b| ≤ β

theorem mixedCosBranchCoordinates_card_le_population {N : ℕ} (b η β : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hβ : β ≤ (Real.sin b) ^ 2 / 8)
    (θ : Fin N → ℝ) :
    ((mixedCosBranchCoordinates b β θ).card : ℝ) ≤
      actualUpperPopulation η θ + actualLowerPopulation η θ := by
  have hpoint (i : Fin N) (hi : i ∈ mixedCosBranchCoordinates b β θ) :
      (1 : ℝ) ≤ upperPeriodicBump η (θ i) + lowerPeriodicBump η (θ i) := by
    rcases cosine_band_bump_plateau b η (θ i) β hη hwidth hβ (Finset.mem_filter.mp hi).2
      with ⟨hp, hm⟩ | ⟨hp, hm⟩ <;> simp only [hp, hm] <;> norm_num
  calc
    _ = ∑ _i ∈ mixedCosBranchCoordinates b β θ, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ mixedCosBranchCoordinates b β θ,
        (upperPeriodicBump η (θ i) + lowerPeriodicBump η (θ i)) := Finset.sum_le_sum hpoint
    _ ≤ ∑ i : Fin N, (upperPeriodicBump η (θ i) + lowerPeriodicBump η (θ i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => add_nonneg (upperPeriodicBump_bounds η (θ i)).1 (lowerPeriodicBump_bounds η (θ i)).1)
    _ = _ := by rw [Finset.sum_add_distrib]; rfl

theorem upperEdgeRoot_near_one_of_argument {W : ℂ} (hW : 0 < W.im)
    (hnear : ‖W - 1‖ ≤ 1 / 32) : ‖1 - upperEdgeRoot W‖ ≤ 1 / 4 := by
  have hh := upperEdgeRoot_boundary_holder 1 (by norm_num) W hW
  have hroot : upperBoundaryRoot 1 = 1 := by simp [upperBoundaryRoot]
  rw [hroot] at hh
  norm_num only [Complex.ofReal_one] at hh
  rw [norm_sub_rev (1 : ℂ)]
  nlinarith [norm_nonneg (upperEdgeRoot W - 1)]

end
end IsingBulk.AnisoF002.Isotropic
