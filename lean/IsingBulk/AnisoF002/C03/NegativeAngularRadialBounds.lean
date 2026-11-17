import IsingBulk.AnisoF002.C03.NegativeAngularMoments

/-!
# The actual radial mass bound used by the angular concentration argument

For every particle number at least three, at least five eighths of the
constructed Gaussian radial law has `Q ≥ n^2/8`.  This is obtained from
its exact inverse moment, without a concentration hypothesis.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem radialShape_gt_one {d : ℕ} (hd : 2 ≤ d) : 1 < radialShape d := by
  rw [radialShape_exact (by omega)]
  have hn : (3 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ d + 1)
  nlinarith

theorem inverse_quadratic_exponent_admissible {d : ℕ} (hd : 2 ≤ d) :
    -1 < (radialPower d : ℝ) + (-2) := by
  have h := radialShape_gt_one hd
  unfold radialShape at h
  linarith

theorem radial_rpow_neg_two (r : Ioi (0 : ℝ)) : r.val ^ (-2 : ℝ) = (r.val ^ 2)⁻¹ := by
  rw [Real.rpow_neg r.property.le, Real.rpow_two]

theorem radialLaw_inverse_quadratic_integrable {d : ℕ} (hd : 2 ≤ d) :
    Integrable (fun r : Ioi (0 : ℝ) => (r.val ^ 2)⁻¹) (radialLaw d) := by
  have h := (radial_rpow_integrable d (-2) (inverse_quadratic_exponent_admissible hd)).smul_measure
    (ENNReal.inv_ne_top.mpr (radialWeighted_mass_pos d).ne')
  simpa only [radial_rpow_neg_two, radialLaw] using h

theorem radialLaw_inverse_quadratic_moment {d : ℕ} (hd : 2 ≤ d) :
    (∫ r : Ioi (0 : ℝ), (r.val ^ 2)⁻¹ ∂radialLaw d) = (radialShape d - 1)⁻¹ := by
  have ha : 0 < radialShape d - 1 := sub_pos.mpr (radialShape_gt_one hd)
  have hg : Real.Gamma (radialShape d - 1) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hrec : Real.Gamma (radialShape d) =
      (radialShape d - 1) * Real.Gamma (radialShape d - 1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one ha.ne'
  calc
    (∫ r : Ioi (0 : ℝ), (r.val ^ 2)⁻¹ ∂radialLaw d) =
        Real.Gamma (radialShape d - 1) / Real.Gamma (radialShape d) := by
      have h := radialLaw_integral_rpow d (-2) (inverse_quadratic_exponent_admissible hd)
      rw [show radialShape d + (-2) / 2 = radialShape d - 1 by ring] at h
      simpa only [radial_rpow_neg_two] using h
    _ = (radialShape d - 1)⁻¹ := by
      rw [hrec]
      field_simp

theorem radialLaw_small_quadratic_mass {d : ℕ} (hd : 2 ≤ d) :
    radialLaw d {r | r.val ^ 2 < (((d + 1 : ℕ) : ℝ) ^ 2 / 8)} ≤ (3 / 8 : ℝ≥0∞) := by
  let n : ℝ := ((d + 1 : ℕ) : ℝ)
  have hn : 3 ≤ n := by dsimp [n]; exact_mod_cast (by omega : 3 ≤ d + 1)
  have hn2 : 0 < n ^ 2 := by positivity
  have hi := (radialLaw_inverse_quadratic_integrable hd).const_mul (n ^ 2 / 8)
  have hnonneg : 0 ≤ᵐ[radialLaw d] (fun r : Ioi (0 : ℝ) => n ^ 2 / 8 * (r.val ^ 2)⁻¹) :=
    Filter.Eventually.of_forall (fun r => by positivity)
  have hbound := hi.measure_le_integral hnonneg
    (s := {r : Ioi (0 : ℝ) | r.val ^ 2 < n ^ 2 / 8}) (by
      intro r hr
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ (sq_pos_of_pos r.property)).mpr (by simpa using hr.le))
  rw [integral_const_mul, radialLaw_inverse_quadratic_moment hd,
    radialShape_exact (by omega)] at hbound
  have hnumeric : n ^ 2 / 8 * ((n ^ 2 - 1) / 2 - 1)⁻¹ ≤ (3 / 8 : ℝ) := by
    have ha : 0 < (n ^ 2 - 1) / 2 - 1 := by nlinarith
    rw [← div_eq_mul_inv, div_le_iff₀ ha]
    nlinarith
  exact hbound.trans (by
    have hh := ENNReal.ofReal_le_ofReal hnumeric
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8),
      ENNReal.ofReal_ofNat] using hh)

theorem radialLaw_large_quadratic_mass {d : ℕ} (hd : 2 ≤ d) :
    (5 / 8 : ℝ≥0∞) ≤ radialLaw d {r | (((d + 1 : ℕ) : ℝ) ^ 2 / 8) ≤ r.val ^ 2} := by
  have h := radialLaw_small_quadratic_mass hd
  have hm : MeasurableSet {r : Ioi (0 : ℝ) | r.val ^ 2 < (((d + 1 : ℕ) : ℝ) ^ 2 / 8)} := by
    measurability
  have hc := prob_add_prob_compl (μ := radialLaw d) hm
  have he : {r : Ioi (0 : ℝ) | r.val ^ 2 < (((d + 1 : ℕ) : ℝ) ^ 2 / 8)}ᶜ =
      {r | (((d + 1 : ℕ) : ℝ) ^ 2 / 8) ≤ r.val ^ 2} := by ext r; simp
  rw [he] at hc
  have hh : (1 : ℝ≥0∞) ≤ 3 / 8 + radialLaw d {r | (((d + 1 : ℕ) : ℝ) ^ 2 / 8) ≤ r.val ^ 2} := by
    rw [← hc]
    exact add_le_add h le_rfl
  have hsub : (1 : ℝ≥0∞) - 3 / 8 ≤
      radialLaw d {r | (((d + 1 : ℕ) : ℝ) ^ 2 / 8) ≤ r.val ^ 2} :=
    tsub_le_iff_right.mpr (by simpa only [add_comm] using hh)
  have hnum : (1 : ℝ≥0∞) - 3 / 8 = 5 / 8 := by
    have hnn : (1 : ℝ≥0) - 3 / 8 = 5 / 8 := by
      apply NNReal.eq
      rw [NNReal.coe_sub (by exact_mod_cast (show (3 : ℝ) / 8 ≤ 1 by norm_num))]
      norm_num
    have hh := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hnn
    simpa only [ENNReal.coe_sub, ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
      ENNReal.coe_one, ENNReal.coe_ofNat] using hh
  rwa [hnum] at hsub

end
end IsingBulk.AnisoF002.NegativeHT.Angular
