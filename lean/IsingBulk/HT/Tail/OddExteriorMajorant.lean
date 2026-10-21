import IsingBulk.HT.Contour.OddMatching
import IsingBulk.Tail.ExteriorReducedMajorant

/-!
# A summable majorant for actual odd offsite form factors

The odd Schur extension supplies one ghost entry.  Its norm is at most one,
and it is not an extra physical particle or an extra contour integration.
The factorial here remains `(2*n+1)!`, precisely the HT normalization.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

/-- Odd-dimensional circle products use the augmented Pfaffian, while
retaining the original physical pair product on the left. -/
theorem odd_circle_pairProduct_matching_bound (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (y : Fin (2 * n + 1) → ℂ)
    (hy : ∀ i, ‖y i‖ = r) :
    ‖IsingBulk.First.pairProduct y‖ ≤
      (matchingCount (n + 1) : ℝ) * (max 1 (2 * r / (1 - r ^ 2))) ^ (n + 1) := by
  apply IsingBulk.HT.Contour.odd_indexed_pairProduct_norm_le_matchings n y
  · intro i j
    exact IsingBulk.Schur.denominator_ne_zero
      (by rw [hy i]; exact hr1) (by rw [hy j]; exact hr1)
  · intro i he
    have hh : ‖y i‖ < 1 := by rw [hy i]; exact hr1
    simp [he] at hh
  · exact le_max_left _ _
  · intro i j
    exact (subdisk_pairKernel_bound hr hr1 (hy i).le (hy j).le).trans
      (le_max_right _ _)

/-- The N=1 case must also be retained in the HT series.  The all-positive
version has gap `1-r`, rather than the LT tail's `1-r^2`. -/
theorem positive_coordinateProduct_gap {N : ℕ} (hN : 0 < N)
    {z : Fin N → ℂ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hz : ∀ i, ‖z i‖ ≤ r) :
    1 - r ≤ ‖1 - coordinateProduct z‖ := by
  have hp : ‖coordinateProduct z‖ ≤ r ^ N := by
    simp only [coordinateProduct, norm_prod]
    calc
      ∏ i, ‖z i‖ ≤ ∏ _i : Fin N, r :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hz i)
      _ = r ^ N := by simp
  have he := pow_le_pow_of_le_one hr hr1.le (show 1 ≤ N by omega)
  have hn := norm_sub_norm_le (1 : ℂ) (coordinateProduct z)
  simp only [norm_one] at hn
  simp only [pow_one] at he
  linarith

/-- The existing reduced-density algebra with the all-positive product
gap.  Root contraction is already an all-dimensional LT theorem. -/
theorem positive_reducedDensity_upper_bound {N : ℕ} (hN : 0 < N) {r A P : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (z y : Fin N → ℂ) (hz : ∀ i, ‖z i‖ ≤ r) (hy : ∀ i, ‖y i‖ = r)
    (hzi : ∀ i, ‖(z i)⁻¹‖ ≤ A)
    (hpairz : ‖IsingBulk.First.pairProduct z‖ ≤ 1)
    (hpairy : ‖IsingBulk.First.pairProduct y‖ ≤ P) :
    ‖reducedDensity z y‖ ≤
      (2 * (max A r⁻¹) ^ N / (1 - r) ^ 2) * P * (2 * r ^ 2 / (1 - r ^ 2)) ^ N := by
  have hg : 0 < 1 - r := sub_pos.mpr hr1
  have hnum := inverse_global_numerator_norm_le hA (inv_nonneg.mpr hr.le) hzi
    (fun i => show ‖(y i)⁻¹‖ ≤ r⁻¹ by rw [norm_inv, hy i])
  have hdz := positive_coordinateProduct_gap hN hr.le hr1 hz
  have hdy := positive_coordinateProduct_gap hN hr.le hr1 (fun i => (hy i).le)
  have hden : (1 - r) ^ 2 ≤ ‖(1 - coordinateProduct z) * (1 - coordinateProduct y)‖ := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hdz hdy hg.le (norm_nonneg _)
  have hglob : ‖((coordinateProduct z)⁻¹ + (coordinateProduct y)⁻¹) /
      ((1 - coordinateProduct z) * (1 - coordinateProduct y))‖ ≤
      2 * (max A r⁻¹) ^ N / (1 - r) ^ 2 := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hg) hden
  have hres : ‖∏ i, residueFactor (z i)‖ ≤ (2 * r ^ 2 / (1 - r ^ 2)) ^ N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, (2 * r ^ 2 / (1 - r ^ 2)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => subdisk_residueFactor_bound hr.le hr1 (hz i))
      _ = _ := by simp [div_pow]
  simp only [reducedDensity, norm_mul]
  calc
    _ ≤ (2 * (max A r⁻¹) ^ N / (1 - r) ^ 2) * 1 * P *
        (2 * r ^ 2 / (1 - r ^ 2)) ^ N := by gcongr
    _ = _ := by ring

/-- The ghost normalization is exact.  No `(2*n+2)!` normalization is
substituted for the physical odd-particle factorial. -/
theorem odd_matching_majorant_identity (n : ℕ) (r H D E g : ℝ) :
    ((2 * n + 1).factorial : ℝ)⁻¹ *
      (r ^ (2 * n + 1) * ((2 * H ^ (2 * n + 1) / g ^ 2) *
        ((matchingCount (n + 1) : ℝ) * D ^ (n + 1)) * E ^ (2 * n + 1))) =
      (2 * r * H * E * D / g ^ 2) *
        (((r * H * E) ^ 2 * D / 2) ^ n / (n.factorial : ℝ)) := by
  have hf : (matchingCount (n + 1) : ℝ) * ((2 : ℝ) ^ n * (n.factorial : ℝ)) =
      ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast IsingBulk.HT.Contour.odd_matchingCount_factorial n
  have hm0 : (matchingCount (n + 1) : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hf
    exact (by positivity : (0 : ℝ) < (2 * n + 1).factorial).ne' hf.symm
  rw [← hf]
  by_cases hg : g = 0
  · simp [hg]
  · simp only [pow_add, pow_one, pow_mul, mul_pow, div_pow]
    field_simp

/-- The actual residue-reduced odd coefficients admit an exponential-series
majorant at every fixed admissible circle, including N=1. -/
theorem odd_doubleFormFactor_exponential_bound (n : ℕ)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : r⁻¹ - r < (sourceS s).im)
    (hi : ∀ y : ℂ, ‖y‖ = r → ‖(globalRoot s y)⁻¹‖ ≤ A) :
    let D := max 1 (2 * r / (1 - r ^ 2))
    let X := r * (max A r⁻¹) * (2 * r ^ 2 / (1 - r ^ 2))
    ‖doubleFormFactor (2 * n + 1) r s‖ ≤
      (2 * X * D / (1 - r) ^ 2) * ((X ^ 2 * D / 2) ^ n / (n.factorial : ℝ)) := by
  dsimp only
  have ha := globalRoot_admissible hr hr1 hm
  rw [residue_reduction (2 * n + 1) (by omega) r hr s (globalRoot s)
    (fun y hy => ha.toTuple (2 * n + 1) y hy)]
  have hb := multiCircleIntegral_norm_le (2 * n + 1) hr.le
    (fun y => reducedDensity (fun i => globalRoot s (y i)) y) (by
      intro y hy
      exact positive_reducedDensity_upper_bound (by omega) hr hr1 hA (by positivity)
        _ y (fun i => (globalRoot_inside_radius hr hr1 hm (hy i)).le) hy
        (fun i => hi (y i) (hy i)) (original_root_pairProduct_norm hr hr1 hm y hy)
        (odd_circle_pairProduct_matching_bound n hr.le hr1 y hy))
  have hnorm := mul_le_mul_of_nonneg_left hb
    (inv_nonneg.mpr (Nat.cast_nonneg (2 * n + 1).factorial))
  simp only [reducedFormFactor, norm_mul, norm_inv, Complex.norm_natCast]
  rw [odd_matching_majorant_identity] at hnorm
  convert hnorm using 1
  ring

end
end IsingBulk.HT.Tail
