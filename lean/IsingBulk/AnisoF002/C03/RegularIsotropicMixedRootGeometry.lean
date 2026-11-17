import IsingBulk.AnisoF002.C03.RegularIsotropicExteriorGap
import IsingBulk.AnisoF002.C03.RegularIsotropicCompactPair

/-!
# Constructed branch and away-pair constants for the entire actual contour

All angular regions and their constants are chosen before N. The true
branch roots lie near one, and every pair with an away coordinate has
a fixed positive denominator gap. No angular competitors are omitted.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail

theorem exists_actual_mixed_root_geometry (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η) :
    ∃ β δ d : ℝ, 0 < β ∧ β ≤ (Real.sin b) ^ 2 / 8 ∧
      0 < δ ∧ δ ≤ 1 ∧ 0 < d ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ∈ Icc 0 δ, ∀ θ : Fin N → ℝ,
        (∀ i, |Real.cos (θ i) - Real.cos b| ≤ β →
          ‖1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i)‖ ≤ 1 / 4) ∧
        (∀ i j, (β < |Real.cos (θ i) - Real.cos b| ∨ β < |Real.cos (θ j) - Real.cos b|) →
          d ≤ ‖1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) *
            isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ j)‖) := by
  let S := 2 * Real.cos α
  have hcosL := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hcosL
  have hS : 0 < S := by dsimp [S]; linarith
  have hsin : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  let β := min (1 / 256) ((Real.sin b) ^ 2 / 16)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβsmall : β ≤ 1 / 256 := min_le_left _ _
  have hβsin : β ≤ (Real.sin b) ^ 2 / 8 :=
    (min_le_right _ _).trans (by nlinarith [sq_nonneg (Real.sin b)])
  let δ := min 1 (min (β / 24) (S / 24))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδβ : δ ≤ β / 24 := (min_le_right _ _).trans (min_le_left _ _)
  have hδS : δ ≤ S / 24 := (min_le_right _ _).trans (min_le_right _ _)
  let c := min 1 (min (β * isotropicRootNormFloor) (S * isotropicRootNormFloor))
  have hc : 0 < c := by dsimp [c]; positivity [isotropicRootNormFloor_pos]
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcβ : c ≤ β * isotropicRootNormFloor := (min_le_right _ _).trans (min_le_left _ _)
  have hcS : c ≤ S * isotropicRootNormFloor := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨d, hd, hpair⟩ := exists_lower_disk_pair_gap_away_endpoints c hc
  refine ⟨β, δ, d, hβ, hβsin, hδ, hδ1, hd, ?_⟩
  intro N hN ε hε hεδ τ hτ θ
  let W : Fin N → ℂ := fun i => isotropicDispersion
    (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i)
  let r : Fin N → ℂ := fun i => isotropicInteriorRoot
    (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i)
  have hSi := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hWi (i : Fin N) : 0 < (W i).im :=
    actual_balanced_homotopy_sheet _ hSi η τ 1 hη hτ.1 zero_le_one θ i
  have hWpert (i : Fin N) : ‖W i - ((S - Real.cos (θ i) : ℝ) : ℂ)‖ ≤ 4 * ε + 2 * τ :=
    actual_balanced_dispersion_perturbation hN α ε η τ hα hε (hεδ.trans hδ1)
      ⟨hτ.1, hτ.2.trans hδ1⟩ θ i
  have herrβ : 4 * ε + 2 * τ ≤ β / 4 := by linarith only [hεδ, hτ.2, hδβ]
  have herrS : 4 * ε + 2 * τ ≤ S / 4 := by linarith only [hεδ, hτ.2, hδS]
  have hrn (i : Fin N) : ‖r i‖ ≤ 1 := (upperEdgeRoot_norm_lt_one (hWi i)).le
  have hri (i : Fin N) : (r i).im ≤ 0 := (upperEdgeRoot_im_neg (Or.inl (hWi i))).le
  have hrlo (i : Fin N) : isotropicRootNormFloor ≤ ‖r i‖ :=
    actual_balanced_root_norm_floor hN _
      hSi (isotropicRadialParameter_norm_le_three α ε hε.le (hεδ.trans hδ1)) hη
      ⟨hτ.1, hτ.2.trans hδ1⟩ θ i
  have hbase (i : Fin N) : ‖(1 : ℂ) - ((S - Real.cos (θ i) : ℝ) : ℂ)‖ =
      |Real.cos (θ i) - Real.cos b| := by
    have he : (1 : ℂ) - ((S - Real.cos (θ i) : ℝ) : ℂ) =
        ((Real.cos (θ i) - Real.cos b : ℝ) : ℂ) := by
      dsimp [S]
      rw [← hpoint]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
  have hplus (i : Fin N) : S / 2 ≤ ‖W i + 1‖ := by
    have hre := Complex.abs_re_le_norm (W i - ((S - Real.cos (θ i) : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    have hlo := (abs_le.mp (hre.trans ((hWpert i).trans herrS))).1
    have hnorm := Complex.re_le_norm (W i + 1)
    simp only [Complex.add_re, Complex.one_re] at hnorm
    linarith [Real.cos_le_one (θ i)]
  have hrplus (i : Fin N) : c ≤ ‖1 + r i‖ := by
    have he := reciprocal_root_distance_neg_one_sq (isotropicInteriorRoot_polynomial
      (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i))
    change ‖1 + r i‖ ^ 2 = 2 * ‖W i + 1‖ * ‖r i‖ at he
    have hm := mul_le_mul (hplus i) (hrlo i) isotropicRootNormFloor_pos.le (norm_nonneg _)
    nlinarith [norm_nonneg (1 + r i)]
  have hfar (i : Fin N) (hi : β < |Real.cos (θ i) - Real.cos b|) : c ≤ ‖1 - r i‖ := by
    have ht := norm_sub_le (W i - ((S - Real.cos (θ i) : ℝ) : ℂ)) (W i - 1)
    have he : (W i - ((S - Real.cos (θ i) : ℝ) : ℂ)) - (W i - 1) =
        (1 : ℂ) - ((S - Real.cos (θ i) : ℝ) : ℂ) := by ring
    rw [he, hbase] at ht
    have harg : β / 2 ≤ ‖W i - 1‖ := by linarith [(hWpert i).trans herrβ]
    have he := reciprocal_root_distance_one_sq (isotropicInteriorRoot_polynomial
      (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i))
    change ‖1 - r i‖ ^ 2 = 2 * ‖W i - 1‖ * ‖r i‖ at he
    have hm := mul_le_mul harg (hrlo i) isotropicRootNormFloor_pos.le (norm_nonneg _)
    nlinarith [norm_nonneg (1 - r i)]
  constructor
  · intro i hi
    have ht := norm_sub_le (W i - ((S - Real.cos (θ i) : ℝ) : ℂ))
      ((1 : ℂ) - ((S - Real.cos (θ i) : ℝ) : ℂ))
    have he : (W i - ((S - Real.cos (θ i) : ℝ) : ℂ)) -
        ((1 : ℂ) - ((S - Real.cos (θ i) : ℝ) : ℂ)) = W i - 1 := by ring
    rw [he, hbase] at ht
    apply upperEdgeRoot_near_one_of_argument (hWi i)
    linarith [(hWpert i).trans herrβ]
  · intro i j hij
    rcases hij with hi | hj
    · exact hpair (r i) (r j) (hrn i) (hrn j) (hri i) (hri j) (hfar i hi) (hrplus i)
    · have hh := hpair (r j) (r i) (hrn j) (hrn i) (hri j) (hri i) (hfar j hj) (hrplus j)
      simpa only [mul_comm (r j) (r i)] using hh

end
end IsingBulk.AnisoF002.Isotropic
