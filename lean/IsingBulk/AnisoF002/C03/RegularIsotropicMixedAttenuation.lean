import IsingBulk.AnisoF002.C03.IsotropicBranchOccupancies
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy

/-!
# Actual scalar attenuation and mixed-population dispersion

The reciprocal polynomial gives a quantitative attenuation estimate for
the actual interior root on every bounded upper-half-plane region.
The complete balanced displacement then yields the mixed population
gain before any particle count or angular configuration is selected.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail

theorem upperEdgeRoot_norm_lower {W : ℂ} (hW : 0 < W.im) {H : ℝ}
    (hH : 0 ≤ H) (hWH : ‖W‖ ≤ H) :
    1 / (2 * H + 1) ≤ ‖upperEdgeRoot W‖ := by
  let r := upperEdgeRoot W
  have hr : ‖r‖ ≤ 1 := (upperEdgeRoot_norm_lt_one hW).le
  have hp := upperEdgeRoot_polynomial W
  have he : (1 : ℂ) = 2 * W * r - r ^ 2 := by
    change r ^ 2 - 2 * W * r + 1 = 0 at hp
    linear_combination hp
  have hn : 1 ≤ 2 * H * ‖r‖ + ‖r‖ ^ 2 := by
    calc
      (1 : ℝ) = ‖2 * W * r - r ^ 2‖ := by rw [← he, norm_one]
      _ ≤ ‖2 * W * r‖ + ‖r ^ 2‖ := norm_sub_le _ _
      _ ≤ 2 * H * ‖r‖ + ‖r‖ ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_two, norm_pow]
        gcongr
  apply (div_le_iff₀ (by positivity : 0 < 2 * H + 1)).mpr
  nlinarith [norm_nonneg r]

/-- A quantitative estimate for the actual spectral root, independent of
an angular model or branch expansion. -/
theorem upperEdgeRoot_log_attenuation {W : ℂ} (hW : 0 < W.im) {H : ℝ}
    (hH : 0 ≤ H) (hWH : ‖W‖ ≤ H) :
    W.im / (2 * H + 1) ^ 2 ≤ -Real.log ‖upperEdgeRoot W‖ := by
  let r := upperEdgeRoot W
  have hr0 : 0 < ‖r‖ := norm_pos_iff.mpr (upperEdgeRoot_ne_zero W)
  have hr1 : ‖r‖ ≤ 1 := (upperEdgeRoot_norm_lt_one hW).le
  have hri : r.im < 0 := upperEdgeRoot_im_neg (Or.inl hW)
  have hri1 : -r.im ≤ 1 := by
    have hh := Complex.abs_im_le_norm r
    rw [abs_of_neg hri] at hh
    exact hh.trans hr1
  have hid := reciprocal_root_imag_identity (upperEdgeRoot_polynomial W) (upperEdgeRoot_ne_zero W)
  rw [Complex.normSq_eq_norm_sq] at hid
  change 2 * W.im * ‖r‖ ^ 2 = r.im * (‖r‖ ^ 2 - 1) at hid
  have hsq : 0 ≤ 1 - ‖r‖ ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hri1 hsq
  have hatten : W.im * ‖r‖ ^ 2 ≤ 1 - ‖r‖ := by
    nlinarith [sq_nonneg (1 - ‖r‖)]
  have hlow := upperEdgeRoot_norm_lower hW hH hWH
  have hlow2 : (1 / (2 * H + 1)) ^ 2 ≤ ‖r‖ ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hlow 2
  have hprod := mul_le_mul_of_nonneg_left hlow2 hW.le
  have hlog := Real.log_le_sub_one_of_pos hr0
  have he : W.im * (1 / (2 * H + 1)) ^ 2 = W.im / (2 * H + 1) ^ 2 := by
    field_simp
  rw [he] at hprod
  change W.im / (2 * H + 1) ^ 2 ≤ -Real.log ‖r‖
  linarith

def actualUpperPopulation {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) : ℝ :=
  ∑ i, upperPeriodicBump η (θ i)

def actualLowerPopulation {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) : ℝ :=
  ∑ i, lowerPeriodicBump η (θ i)

theorem actualUpperPopulation_nonneg {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) :
    0 ≤ actualUpperPopulation η θ := Finset.sum_nonneg (fun i _ => (upperPeriodicBump_bounds η (θ i)).1)

theorem actualLowerPopulation_nonneg {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) :
    0 ≤ actualLowerPopulation η θ := Finset.sum_nonneg (fun i _ => (lowerPeriodicBump_bounds η (θ i)).1)

theorem actualUpperPopulation_eq_occupancy {N : ℕ} (hN : 0 < N) (η : ℝ) (θ : Fin N → ℝ) :
    actualUpperPopulation η θ = N * actualUpperOccupancy η θ := by
  unfold actualUpperPopulation actualUpperOccupancy
  field_simp

theorem actualLowerPopulation_eq_occupancy {N : ℕ} (hN : 0 < N) (η : ℝ) (θ : Fin N → ℝ) :
    actualLowerPopulation η θ = N * actualLowerOccupancy η θ := by
  unfold actualLowerPopulation actualLowerOccupancy
  field_simp

theorem upperPeriodicBump_sine_lower {η : ℝ} (hη : 0 < η) (θ : ℝ) :
    η * upperPeriodicBump η θ ≤ upperPeriodicBump η θ * Real.sin θ := by
  by_cases hθ : Real.sin θ ≤ η
  · rw [upperPeriodicBump_zero hη hθ]
    simp
  · nlinarith [upperPeriodicBump_bounds η θ, lt_of_not_ge hθ]

theorem lowerPeriodicBump_sine_upper {η : ℝ} (hη : 0 < η) (θ : ℝ) :
    lowerPeriodicBump η θ * Real.sin θ ≤ -η * lowerPeriodicBump η θ := by
  have h := upperPeriodicBump_sine_lower hη (-θ)
  rw [Real.sin_neg] at h
  change upperPeriodicBump η (-θ) * Real.sin θ ≤ -η * upperPeriodicBump η (-θ)
  nlinarith

theorem neg_sinh_mul_ge_neg_mul {h s : ℝ} (hs : h * s ≤ 0) :
    -h * s ≤ -Real.sinh h * s := by
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have hs0 : 0 ≤ s := by nlinarith
    have hsin := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ -h)
    rw [Real.sinh_neg] at hsin
    nlinarith [mul_le_mul_of_nonneg_right hsin hs0]
  · simp
  · have hs0 : s ≤ 0 := by nlinarith
    have hsin := Real.self_le_sinh_iff.mpr hh.le
    nlinarith [mul_le_mul_of_nonpos_right hsin hs0]

theorem actual_balanced_dispersion_im_lower {N : ℕ} (hN : 0 < N)
    (S : ℂ) {η τ : ℝ} (hη : 0 < η) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i : Fin N) :
    S.im + (η * τ / N) *
      (actualUpperPopulation η θ * lowerPeriodicBump η (θ i) +
        actualLowerPopulation η θ * upperPeriodicBump η (θ i)) ≤
      (isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i)).im := by
  let P := actualUpperPopulation η θ
  let Q := actualLowerPopulation η θ
  let p := upperPeriodicBump η (θ i)
  let m := lowerPeriodicBump η (θ i)
  let h := (τ / N) * (P * m - Q * p)
  have hP : 0 ≤ P := actualUpperPopulation_nonneg η θ
  have hQ : 0 ≤ Q := actualLowerPopulation_nonneg η θ
  have hp := upperPeriodicBump_sine_lower hη (θ i)
  have hm := lowerPeriodicBump_sine_upper hη (θ i)
  have hps := mul_le_mul_of_nonneg_left hp hQ
  have hms := mul_le_mul_of_nonneg_left hm hP
  have hs : h * Real.sin (θ i) ≤ 0 := by
    have hh := balancedShift_sine_nonpos (τ / N) θ
      (fun j => upperPeriodicBump η (θ j)) (fun j => lowerPeriodicBump η (θ j))
      (by positivity) (fun j => (upperPeriodicBump_bounds η (θ j)).1)
      (fun j => (lowerPeriodicBump_bounds η (θ j)).1)
      (fun j => (actual_bump_sine_signs hη (θ j)).1)
      (fun j => (actual_bump_sine_signs hη (θ j)).2) i
    exact hh
  have hlin : (η * τ / N) * (P * m + Q * p) ≤ -h * Real.sin (θ i) := by
    have hh := mul_le_mul_of_nonneg_left (show η * (P * m + Q * p) ≤
      Q * (p * Real.sin (θ i)) - P * (m * Real.sin (θ i)) by
        dsimp [p, m]
        nlinarith) (show 0 ≤ τ / (N : ℝ) by positivity)
    dsimp only [h]
    convert hh using 1 <;> ring
  have hangle : actualHomotopyAngle η τ 1 θ i = (θ i : ℂ) - Complex.I * (h : ℂ) := by
    simp only [actualHomotopyAngle, balancedHomotopyCoordinate, contourCoordinate,
      one_mul, balancedShift, Fintype.card_fin]
    rfl
  rw [hangle, isotropicDispersion_contour_im]
  have hsin := neg_sinh_mul_ge_neg_mul hs
  change S.im + (η * τ / N) * (P * m + Q * p) ≤ _
  linarith

theorem actual_balanced_total_dispersion_im_lower {N : ℕ} (hN : 0 < N)
    (S : ℂ) {η τ : ℝ} (hη : 0 < η) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) :
    N * S.im + (2 * η * τ / N) * actualUpperPopulation η θ * actualLowerPopulation η θ ≤
      ∑ i, (isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i)).im := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => actual_balanced_dispersion_im_lower hN S hη hτ θ i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  change N * S.im + (2 * η * τ / N) * (∑ i, upperPeriodicBump η (θ i)) *
    (∑ i, lowerPeriodicBump η (θ i)) ≤ _
  dsimp only [actualUpperPopulation, actualLowerPopulation] at h
  convert h using 1
  ring

end
end IsingBulk.AnisoF002.Isotropic
