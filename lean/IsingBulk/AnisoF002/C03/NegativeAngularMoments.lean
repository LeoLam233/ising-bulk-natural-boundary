import IsingBulk.AnisoF002.C03.NegativeAngularGamma

/-!
# Exact moments of the actual constrained Gaussian radius

The real exponent formula covers both all positive integer moments of
`Q = r^2` and the inverse moment used to keep a fixed fraction of the
radial mass above `n^2 / 8` in frozen F002, Lemma 4.2.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem radialLebesgueWeight_mul_rpow (d : ℕ) (t : ℝ) (r : Ioi (0 : ℝ)) :
    radialLebesgueWeight d r * r.val ^ t =
      r.val ^ ((radialPower d : ℝ) + t) * Real.exp (-r.val ^ 2) := by
  rw [Real.rpow_add r.property, Real.rpow_natCast]
  unfold radialLebesgueWeight
  ring

theorem radial_rpow_integrable (d : ℕ) (t : ℝ)
    (ht : -1 < (radialPower d : ℝ) + t) :
    Integrable (fun r : Ioi (0 : ℝ) => r.val ^ t) (radialWeighted d) := by
  have h : IntegrableOn
      (fun x : ℝ => x ^ ((radialPower d : ℝ) + t) * Real.exp (-x ^ 2)) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one ht)
  have hc := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h
  rw [radialWeighted_eq_Lebesgue_density]
  apply (integrable_withDensity_iff_integrable_smul'
    (continuous_radialLebesgueWeight d).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  convert hc using 1
  · ext r
    rw [ENNReal.toReal_ofReal (radialLebesgueWeight_pos d r).le, smul_eq_mul,
      radialLebesgueWeight_mul_rpow]
    rfl
  · rfl

theorem radialWeighted_integral_rpow (d : ℕ) (t : ℝ)
    (ht : -1 < (radialPower d : ℝ) + t) :
    (∫ r : Ioi (0 : ℝ), r.val ^ t ∂radialWeighted d) =
      (1 / 2 : ℝ) * Real.Gamma (radialShape d + t / 2) := by
  rw [radialWeighted_eq_Lebesgue_density,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_radialLebesgueWeight d).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (radialLebesgueWeight_pos d _).le, smul_eq_mul,
    radialLebesgueWeight_mul_rpow]
  change (∫ r : Ioi (0 : ℝ),
      (fun x : ℝ => x ^ ((radialPower d : ℝ) + t) * Real.exp (-x ^ 2)) r.val
        ∂volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) = _
  rw [integral_subtype_comap measurableSet_Ioi
    (fun x : ℝ => x ^ ((radialPower d : ℝ) + t) * Real.exp (-x ^ 2))]
  have h := integral_rpow_mul_exp_neg_rpow (p := 2)
    (q := (radialPower d : ℝ) + t) (by norm_num) ht
  rw [show ((radialPower d : ℝ) + t + 1) / 2 = radialShape d + t / 2 by
    unfold radialShape; ring] at h
  simpa only [Real.rpow_two] using h

theorem radialLaw_integral_rpow (d : ℕ) (t : ℝ)
    (ht : -1 < (radialPower d : ℝ) + t) :
    (∫ r : Ioi (0 : ℝ), r.val ^ t ∂radialLaw d) =
      Real.Gamma (radialShape d + t / 2) / Real.Gamma (radialShape d) := by
  rw [radialLaw, integral_smul_measure, ENNReal.toReal_inv, radialWeighted_mass_gamma,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
      (Real.Gamma_pos_of_pos (radialShape_pos d)).le), smul_eq_mul,
    radialWeighted_integral_rpow d t ht]
  field_simp

theorem gamma_ratio_nat_product {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.Gamma (a + k) / Real.Gamma a = ∏ j ∈ Finset.range k, (a + j) := by
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  induction k with
  | zero => simp [hg]
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity),
      Finset.prod_range_succ, mul_div_assoc, ih]
    ring

theorem radialLaw_quadratic_moment (d k : ℕ) :
    (∫ r : Ioi (0 : ℝ), (r.val ^ 2) ^ k ∂radialLaw d) =
      ∏ j ∈ Finset.range k, (radialShape d + j) := by
  have ht : -1 < (radialPower d : ℝ) + (2 * k : ℕ) := by
    have h := Nat.cast_nonneg (α := ℝ) (radialPower d)
    have h' := Nat.cast_nonneg (α := ℝ) (2 * k)
    linarith
  have h := radialLaw_integral_rpow d (2 * k : ℕ) ht
  have he : ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) := by push_cast; ring
  rw [he, gamma_ratio_nat_product (radialShape_pos d)] at h
  simpa only [Real.rpow_natCast, pow_mul] using h

end
end IsingBulk.AnisoF002.NegativeHT.Angular
