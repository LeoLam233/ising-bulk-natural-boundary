import IsingBulk.AnisoF002.C03.RegularIsotropicMixedRootGeometry
import IsingBulk.AnisoF002.C03.RegularIsotropicSameSidePairs

/-!
# The actual opposite-branch complete-pair estimate

The true upper and lower branch populations occur together in the
denominator. Consequently each exceptional matched pair pays N/B0,
where B0 counts all branch coordinates of the actual angular tuple.
No constraint or winding sector is removed.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators Classical
open IsingBulk.AnisoF002.RegularTail

theorem actualHomotopyAngle_im_abs_le {N : ℕ} (hN : 0 < N)
    (η τ : ℝ) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i : Fin N) :
    |(actualHomotopyAngle η τ 1 θ i).im| ≤ τ := by
  have h := Complex.abs_im_le_norm (actualHomotopyAngle η τ 1 θ i - (θ i : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
  exact h.trans (actual_balanced_homotopy_displacement η τ 1 hτ (by norm_num) θ
    (by simpa only [Fintype.card_fin] using hN) i)

theorem upperPeriodicBump_one_sin_pos {η θ : ℝ} (hη : 0 < η)
    (hp : upperPeriodicBump η θ = 1) : 0 < Real.sin θ := by
  by_contra h
  have hz := upperPeriodicBump_zero hη ((le_of_not_gt h).trans hη.le)
  rw [hp] at hz
  norm_num at hz

theorem lowerPeriodicBump_one_sin_neg {η θ : ℝ} (hη : 0 < η)
    (hp : lowerPeriodicBump η θ = 1) : Real.sin θ < 0 := by
  have h := upperPeriodicBump_one_sin_pos hη hp
  rw [Real.sin_neg] at h
  linarith

theorem actual_opposite_branch_pair_gap_sq {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) (η τ : ℝ)
    (hη : 0 < η) (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ) (i j : Fin N)
    (hpi : upperPeriodicBump η (θ i) = 1) (hmi : lowerPeriodicBump η (θ i) = 0)
    (hpj : upperPeriodicBump η (θ j) = 0) (hmj : lowerPeriodicBump η (θ j) = 1)
    (hri : ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)‖ ≤ 1 / 4)
    (hrj : ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j)‖ ≤ 1 / 4) :
    (isotropicRootNormFloor * η * τ / 8) *
      ((actualUpperPopulation η θ + actualLowerPopulation η θ) / N) ≤
        ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) *
          isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j)‖ ^ 2 := by
  have hWi := actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.1 zero_le_one θ i
  have hWj := actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.1 zero_le_one θ j
  have hi := actual_balanced_dispersion_im_lower hN S hη hτ.1 θ i
  have hj := actual_balanced_dispersion_im_lower hN S hη hτ.1 θ j
  simp only [hpi, hmi, hpj, hmj, mul_zero, mul_one, zero_add, add_zero] at hi hj
  have hsum : (η * τ / N) * (actualUpperPopulation η θ + actualLowerPopulation η θ) ≤
      (isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i)).im +
        (isotropicDispersion (S, actualHomotopyAngle η τ 1 θ j)).im := by nlinarith
  have hgap := near_one_pair_gap_of_imaginary_parts isotropicRootNormFloor_pos.le
    (isotropicInteriorRoot_polynomial (S, actualHomotopyAngle η τ 1 θ i))
    (isotropicInteriorRoot_polynomial (S, actualHomotopyAngle η τ 1 θ j))
    (actual_balanced_root_norm_floor hN S hSi hSn hη hτ θ i)
    (actual_balanced_root_norm_floor hN S hSi hSn hη hτ θ j)
    (upperEdgeRoot_norm_le_one (Or.inl hWi)) (upperEdgeRoot_norm_le_one (Or.inl hWj))
    (upperEdgeRoot_im_neg (Or.inl hWi)).le (upperEdgeRoot_im_neg (Or.inl hWj)).le hri hrj
  apply le_trans _ hgap
  convert mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ isotropicRootNormFloor / 8 by positivity [isotropicRootNormFloor_pos]) using 1
  ring

theorem actual_opposite_branch_pair_weighted {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) (b η β τ : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hβ : β ≤ (Real.sin b) ^ 2 / 8)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (θ : Fin N → ℝ) (i j : Fin N)
    (hi : i ∈ mixedCosBranchCoordinates b β θ) (hj : j ∈ mixedCosBranchCoordinates b β θ)
    (hpi : upperPeriodicBump η (θ i) = 1) (hmi : lowerPeriodicBump η (θ i) = 0)
    (hpj : upperPeriodicBump η (θ j) = 0) (hmj : lowerPeriodicBump η (θ j) = 1)
    (hri : ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)‖ ≤ 1 / 4)
    (hrj : ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j)‖ ≤ 1 / 4) :
    ‖canceledPair 1 (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i))
      (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j))
      (Complex.exp (actualHomotopyAngle η τ 1 θ i * Complex.I))
      (Complex.exp (actualHomotopyAngle η τ 1 θ j * Complex.I))‖ ≤
        (32 * Real.exp 1 ^ 2 / (isotropicRootNormFloor * η * τ)) *
          mixedVertexWeight (mixedCosBranchCoordinates b β θ) i *
          mixedVertexWeight (mixedCosBranchCoordinates b β θ) j := by
  let B0 := ((mixedCosBranchCoordinates b β θ).card : ℝ)
  have hB0 : 0 < B0 := by
    dsimp [B0]
    exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount := mixedCosBranchCoordinates_card_le_population b η β hη hwidth hβ θ
  have hgap := actual_opposite_branch_pair_gap_sq hN S hSi hSn η τ hη ⟨hτ.le, hτ1⟩
    θ i j hpi hmi hpj hmj hri hrj
  have hgap' : (isotropicRootNormFloor * η * τ / 8) * (B0 / N) ≤
      ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) *
        isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j)‖ ^ 2 := by
    apply le_trans _ hgap
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcount hN0.le)
      (by positivity [isotropicRootNormFloor_pos])
  have hLo : 0 < (isotropicRootNormFloor * η * τ / 8) * (B0 / N) := by
    positivity [isotropicRootNormFloor_pos]
  have hb := canceledPair_norm_bound_by_gap
    (upperEdgeRoot_norm_le_one (Or.inl (actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.le zero_le_one θ i)))
    (upperEdgeRoot_norm_le_one (Or.inl (actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.le zero_le_one θ j)))
    ((actualHomotopyAngle_im_abs_le hN η τ hτ.le θ i).trans hτ1)
    ((actualHomotopyAngle_im_abs_le hN η τ hτ.le θ j).trans hτ1)
  apply hb.trans
  apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ 4 * Real.exp 1 ^ 2) hLo hgap').trans_eq
  simp only [mixedVertexWeight, ite_eq_left hi, ite_eq_left hj]
  have hs : Real.sqrt ((N : ℝ) / B0) ^ 2 = (N : ℝ) / B0 := Real.sq_sqrt (by positivity)
  change (4 * Real.exp 1 ^ 2) / ((isotropicRootNormFloor * η * τ / 8) * (B0 / N)) =
    (32 * Real.exp 1 ^ 2 / (isotropicRootNormFloor * η * τ)) *
      Real.sqrt ((N : ℝ) / B0) * Real.sqrt ((N : ℝ) / B0)
  calc
    _ = (32 * Real.exp 1 ^ 2 / (isotropicRootNormFloor * η * τ)) * ((N : ℝ) / B0) := by
      field_simp
      ring
    _ = _ := by
      linear_combination -(32 * Real.exp 1 ^ 2 / (isotropicRootNormFloor * η * τ)) * hs

end
end IsingBulk.AnisoF002.Isotropic
