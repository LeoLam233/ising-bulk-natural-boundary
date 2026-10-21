import IsingBulk.HT.Final.PhysicalTemperature
import IsingBulk.HT.First.NegativePrimeFamily

/-! Actual nonzero HT physical factors at both original selected prime
families, using the same inverse-temperature branch in both quadrants. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.Final IsingBulk.HT.First IsingBulk.PrimeFamily

theorem second_quadrant_pow_four_ne_one {z : ℂ} (hr : z.re < 0) (hi : 0 < z.im) :
    z^4 ≠ 1 := by
  have h := first_quadrant_pow_four_ne_one (z := -star z)
    (by simpa using neg_pos.mpr hr) (by simpa using hi)
  intro he
  apply h
  simp only [neg_pow,show (-1:ℂ)^4=1 by norm_num,one_mul,← star_pow,he,star_one]

theorem selected_positive_nonaxis {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) :
    (selectedPoint p a b)^4 ≠ 1 ∧ (selectedPoint p a b).re ≠ 0 := by
  have hc := cosineAverage_bounds ha hb
  have hr : 0 < (selectedPoint p a b).re := by
    rw [selectedPoint,Complex.exp_ofReal_mul_I_re,Real.cos_arccos (by linarith) hc.2.le]
    exact hc.1
  have hi : 0 < (selectedPoint p a b).im := by
    rw [selectedPoint,Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hc.2)
      (Real.arccos_lt_pi.mpr (by linarith))
  exact ⟨first_quadrant_pow_four_ne_one hr hi,hr.ne'⟩

theorem selected_negative_nonaxis {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    (selectedPoint p a b)^4 ≠ 1 ∧ (selectedPoint p a b).re ≠ 0 := by
  have hc := negative_cosineAverage_bounds ha hb
  have hr : (selectedPoint p a b).re < 0 := by
    rw [selectedPoint,Complex.exp_ofReal_mul_I_re,Real.cos_arccos hc.1.le (by linarith)]
    exact hc.2
  have hi : 0 < (selectedPoint p a b).im := by
    rw [selectedPoint,Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (by linarith))
      (Real.arccos_lt_pi.mpr hc.1)
  exact ⟨second_quadrant_pow_four_ne_one hr hi,hr.ne⟩

/-- Both selected families lie on the same nonzero local physical branch.
The real-coupling assumption is the physical J>0, not a sign of the chart. -/
theorem full_physical_factor_regular_unit {J : ℝ} (hJ : 0 < J)
    {z : ℂ} (hz : ‖z‖=1) (hfour : z^4 ≠ 1) (hre : z.re ≠ 0) :
    AnalyticAt ℂ (fun t => inverseTemperatureBranch J (t⁻¹)*exteriorPrefactor t) z ∧
      inverseTemperatureBranch J (z⁻¹)*exteriorPrefactor z ≠ 0 := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hi : ‖z⁻¹‖=1 := by rw [norm_inv,hz,inv_one]
  have hir : (z⁻¹).re ≠ 0 := by
    simpa only [Complex.inv_re,Complex.normSq_eq_norm_sq,hz,one_pow,div_one] using hre
  obtain ⟨hb,hbn⟩ := inverseTemperatureBranch_regular_unit_nonimaginary hJ hi hir
  obtain ⟨hp,hpn⟩ := exteriorPrefactor_regular_at_unit_nonaxis hz hfour
  exact ⟨(hb.comp (analyticAt_id.inv hz0)).mul hp,mul_ne_zero hbn hpn⟩

theorem selected_positive_physical_factor_regular {J : ℝ} (hJ : 0 < J)
    {p : ℕ} {a b : ℤ} (ha : Admissible p a) (hb : Admissible p b) :
    AnalyticAt ℂ (fun t => inverseTemperatureBranch J (t⁻¹)*exteriorPrefactor t)
      (selectedPoint p a b) ∧
      inverseTemperatureBranch J ((selectedPoint p a b)⁻¹)*
        exteriorPrefactor (selectedPoint p a b) ≠ 0 :=
  full_physical_factor_regular_unit hJ (Complex.norm_exp_ofReal_mul_I _)
    (selected_positive_nonaxis ha hb).1 (selected_positive_nonaxis ha hb).2

theorem selected_negative_physical_factor_regular {J : ℝ} (hJ : 0 < J)
    {p : ℕ} {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    AnalyticAt ℂ (fun t => inverseTemperatureBranch J (t⁻¹)*exteriorPrefactor t)
      (selectedPoint p a b) ∧
      inverseTemperatureBranch J ((selectedPoint p a b)⁻¹)*
        exteriorPrefactor (selectedPoint p a b) ≠ 0 :=
  full_physical_factor_regular_unit hJ (Complex.norm_exp_ofReal_mul_I _)
    (selected_negative_nonaxis ha hb).1 (selected_negative_nonaxis ha hb).2

end
end IsingBulk.HT.Final
