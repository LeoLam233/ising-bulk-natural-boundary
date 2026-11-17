import IsingBulk.AnisoF002.C03.RegularIsotropicMixedRootGeometry
import IsingBulk.AnisoF002.C03.RegularIsotropicPopulationSplit

/-!
# A complete reciprocal-denominator lower bound on the actual mixed support

The deliberately coarse 1/N lower bound applies simultaneously to
every pair, including self pairs. It is sufficient for the protected
c/N^6 complex disk and every fixed-order Cauchy estimate.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail

theorem exists_actual_mixed_pair_gap (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      ∃ g : ℝ, 0 < g ∧ ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ θ : Fin N → ℝ, 1 / 4 ≤ actualUpperPopulation η θ →
        1 / 4 ≤ actualLowerPopulation η θ → ∀ i j,
        g / N ≤ ‖1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) *
          isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ j)‖ := by
  obtain ⟨β, δ, d, _, hβsin, hδ, hδ1, hd, hgeom⟩ :=
    exists_actual_mixed_root_geometry α b η hα hb hpoint hη
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro τ hτ hτδ
  let a := isotropicRootNormFloor * η * τ / 16
  have ha : 0 < a := by dsimp [a]; positivity [isotropicRootNormFloor_pos]
  let g := min d (min 1 a)
  have hg : 0 < g := by dsimp [g]; positivity
  have hgd : g ≤ d := min_le_left _ _
  have hg1 : g ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hga : g ≤ a := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨g, hg, ?_⟩
  intro N hN ε hε hεδ θ hP hQ i j
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hτ1 : τ ≤ 1 := hτδ.trans hδ1
  let S := isotropicRadialParameter α ε
  let W : Fin N → ℂ := fun k => isotropicDispersion (S, actualHomotopyAngle η τ 1 θ k)
  let r : Fin N → ℂ := fun k => isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ k)
  have hSi : 0 < S.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hSn : ‖S‖ ≤ 3 := isotropicRadialParameter_norm_le_three α ε hε.le (hεδ.trans hδ1)
  have hWi (k : Fin N) : 0 < (W k).im :=
    actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.le zero_le_one θ k
  have hrlo (k : Fin N) : isotropicRootNormFloor ≤ ‖r k‖ :=
    actual_balanced_root_norm_floor hN S hSi hSn hη ⟨hτ.le, hτ1⟩ θ k
  obtain ⟨hnear, haway⟩ := hgeom N hN ε hε hεδ τ ⟨hτ.le, hτδ⟩ θ
  have hnormal (k : Fin N) (hk : |Real.cos (θ k) - Real.cos b| ≤ β) :
      η * τ / (4 * N) ≤ (W k).im := by
    have hl := actual_balanced_dispersion_im_lower hN S hη hτ.le θ k
    rcases cosine_band_bump_plateau b η (θ k) β hη hwidth hβsin hk with ⟨hp, hm⟩ | ⟨hp, hm⟩
    · simp only [hp, hm, mul_zero, mul_one, zero_add] at hl
      have hh := mul_le_mul_of_nonneg_left hQ (show 0 ≤ η * τ / N by positivity)
      have he : (η * τ / (N : ℝ)) * (1 / 4) = η * τ / (4 * N) := by ring
      rw [he] at hh
      linarith
    · simp only [hp, hm, mul_zero, mul_one, add_zero] at hl
      have hh := mul_le_mul_of_nonneg_left hP (show 0 ≤ η * τ / N by positivity)
      have he : (η * τ / (N : ℝ)) * (1 / 4) = η * τ / (4 * N) := by ring
      rw [he] at hh
      linarith
  by_cases hi : |Real.cos (θ i) - Real.cos b| ≤ β
  · by_cases hj : |Real.cos (θ j) - Real.cos b| ≤ β
    · have hsq := near_one_pair_gap_of_imaginary_parts isotropicRootNormFloor_pos.le
        (isotropicInteriorRoot_polynomial (S, actualHomotopyAngle η τ 1 θ i))
        (isotropicInteriorRoot_polynomial (S, actualHomotopyAngle η τ 1 θ j))
        (hrlo i) (hrlo j)
        (upperEdgeRoot_norm_le_one (Or.inl (hWi i))) (upperEdgeRoot_norm_le_one (Or.inl (hWi j)))
        (upperEdgeRoot_im_neg (Or.inl (hWi i))).le (upperEdgeRoot_im_neg (Or.inl (hWi j))).le
        (hnear i hi) (hnear j hj)
      have harg : a / N ≤ ‖1 - r i * r j‖ ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left (add_le_add (hnormal i hi) (hnormal j hj))
          (show 0 ≤ isotropicRootNormFloor / 8 by positivity [isotropicRootNormFloor_pos])
        apply le_trans _ hsq
        convert hh using 1
        dsimp [a]
        ring
      have hsqg : g ^ 2 ≤ a * N := by nlinarith
      have hratio : (g / (N : ℝ)) ^ 2 ≤ a / N := by
        have hh := div_le_div_of_nonneg_right hsqg (sq_nonneg (N : ℝ))
        convert hh using 1 <;> field_simp
      have h0 : 0 ≤ g / (N : ℝ) := by positivity
      have hnorm := norm_nonneg (1 - r i * r j)
      change g / N ≤ ‖1 - r i * r j‖
      nlinarith [hratio.trans harg]
    · exact (div_le_self hg.le hN1).trans (hgd.trans (haway i j (Or.inr (lt_of_not_ge hj))))
  · exact (div_le_self hg.le hN1).trans (hgd.trans (haway i j (Or.inl (lt_of_not_ge hi))))

end
end IsingBulk.AnisoF002.Isotropic
