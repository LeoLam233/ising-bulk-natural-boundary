import IsingBulk.Anisotropic.NegativeNormalForm.BetaDensity
import IsingBulk.Anisotropic.NegativeDominance.ExactGamma

/-! Uniform comparison of actual beta masses at simultaneously growing orders. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open IsingBulk.Anisotropic.NegativeDominance

def betaMass (a j : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x^(a-1)/(1+x)^(j+1)

theorem betaMass_eq_product (a j : ℕ) (ha : 0<a) (haj : a≤j) :
    betaMass a j = Real.Gamma a / risingProduct ((j : ℝ)+1-a) a := by
  rw [betaMass, betaPrime_gamma a j ha haj, mul_div_assoc, gamma_jet_ratio a j haj]
  rfl

theorem betaMass_pos (a j : ℕ) (ha : 0<a) (haj : a≤j) : 0 < betaMass a j := by
  rw [betaMass_eq_product a j ha haj]
  have ha' : (0 : ℝ)<a := by exact_mod_cast ha
  have haj' : (a : ℝ)≤j := by exact_mod_cast haj
  exact div_pos (Real.Gamma_pos_of_pos ha') (risingProduct_pos (by linarith) a)

theorem betaMass_ratio (a J j : ℕ) (ha : 0<a) (haJ : a≤J) (haj : a≤j) :
    betaMass a J / betaMass a j =
      risingProduct ((j : ℝ)+1-a) a / risingProduct ((J : ℝ)+1-a) a := by
  rw [betaMass_eq_product a J ha haJ, betaMass_eq_product a j ha haj]
  have hg : Real.Gamma (a : ℝ) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by exact_mod_cast ha))
  field_simp

/-- The exact gamma quotient gives the 4^α mass comparison used in the tail
argument; α and j both vary. No fixed-α asymptotic is used. -/
theorem betaMass_half_order_ratio (a j : ℕ) (ha : 0<a) (hj : 4*a+4≤j) :
    betaMass a (j/2) / betaMass a j ≤ 4^a := by
  have haJ : a≤j/2 := by omega
  have haj : a≤j := by omega
  rw [betaMass_ratio a (j/2) j ha haJ haj]
  have hJ : 0 < ((j/2 : ℕ) : ℝ)+1-a := by
    have h : (a : ℝ) ≤ ((j/2 : ℕ) : ℝ) := by exact_mod_cast haJ
    linarith
  apply (div_le_iff₀ (risingProduct_pos hJ a)).2
  have he : (4:ℝ)^a*risingProduct (((j/2 : ℕ) : ℝ)+1-a) a =
      ∏ k ∈ Finset.range a, 4*(((j/2 : ℕ) : ℝ)+1-a+k) := by
    simp [risingProduct, Finset.prod_mul_distrib]
  rw [he]
  apply Finset.prod_le_prod₀
  · intro k _
    have h : (a : ℝ)≤j := by exact_mod_cast haj
    have hk0 : (0 : ℝ) ≤ k := by positivity
    linarith
  · intro k hk
    have hjJ : (j : ℝ)≤2*((j/2 : ℕ) : ℝ)+1 := by
      exact_mod_cast (show j≤2*(j/2)+1 by omega)
    have hJa : 2*(a : ℝ)+2≤((j/2 : ℕ) : ℝ) := by
      exact_mod_cast (show 2*a+2≤j/2 by omega)
    have hk0 : (0 : ℝ)≤k := by positivity
    linarith


theorem beta_integrable_order (a j : ℕ) (ha : 0<a) (haj : a≤j) :
    IntegrableOn (fun x : ℝ => x^(a-1)/(1+x)^(j+1)) (Ioi 0) :=
  Integrable.of_integral_ne_zero (ne_of_gt (betaMass_pos a j ha haj))

theorem beta_tail_pointwise (a J j : ℕ) (hJj : J≤j) {delta x : ℝ}
    (hd : 0≤delta) (hx : delta≤x) :
    x^(a-1)/(1+x)^(j+1) ≤
      (1+delta)^(-((j-J : ℕ) : ℤ)) * (x^(a-1)/(1+x)^(J+1)) := by
  have hx0 : 0≤x := hd.trans hx
  have hd1 : 0<1+delta := by linarith
  have hx1 : 0<1+x := by linarith
  have he : j+1=(j-J)+(J+1) := by omega
  rw [he, pow_add, zpow_neg, zpow_natCast]
  have hp : (1+delta)^(j-J)≤(1+x)^(j-J) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hi : ((1+x)^(j-J))⁻¹≤((1+delta)^(j-J))⁻¹ :=
    inv_le_inv₀ (by positivity) (by positivity) |>.2 hp
  have h := mul_le_mul_of_nonneg_right hi
    (show 0≤x^(a-1)/(1+x)^(J+1) by positivity)
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using h

/-- Actual omitted beta tail, before the 4^α comparison. -/
theorem beta_tail_ratio (a J j : ℕ) (ha : 0<a) (haJ : a≤J) (hJj : J≤j)
    (delta : ℝ) (hd : 0≤delta) :
    (∫ x in Ioi delta, x^(a-1)/(1+x)^(j+1)) / betaMass a j ≤
      (1+delta)^(-((j-J : ℕ) : ℤ)) * (betaMass a J / betaMass a j) := by
  have hfJ := beta_integrable_order a J ha haJ
  have hfj := beta_integrable_order a j ha (haJ.trans hJj)
  have hsub : Ioi delta ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_le_of_lt hd hx
  have hc : 0≤(1+delta)^(-((j-J : ℕ) : ℤ)) := by positivity
  have hpoint := integral_mono_ae (hfj.mono_set hsub) ((hfJ.mono_set hsub).const_mul ((1+delta)^(-((j-J : ℕ) : ℤ)))) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact beta_tail_pointwise a J j hJj hd (le_of_lt hx))
  rw [integral_const_mul] at hpoint
  have hmass : (∫ x in Ioi delta, x^(a-1)/(1+x)^(J+1)) ≤ betaMass a J := by
    apply setIntegral_mono_set hfJ
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0<x := hx
      positivity
    · exact Filter.Eventually.of_forall (fun x hx => hsub hx)
  have h := hpoint.trans (mul_le_mul_of_nonneg_left hmass hc)
  have hm : 0<betaMass a j := betaMass_pos a j ha (haJ.trans hJj)
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hm.le

/-- Uniform exponentially small omitted beta tail at growing α. -/
theorem beta_tail_half_order (a j : ℕ) (ha : 0<a) (hj : 4*a+4≤j)
    (delta : ℝ) (hd : 0≤delta) :
    (∫ x in Ioi delta, x^(a-1)/(1+x)^(j+1)) / betaMass a j ≤
      (1+delta)^(-((j-j/2 : ℕ) : ℤ))*4^a := by
  exact (beta_tail_ratio a (j/2) j ha (by omega) (by omega) delta hd).trans
    (mul_le_mul_of_nonneg_left (betaMass_half_order_ratio a j ha hj) (by positivity))

end
end IsingBulk.Anisotropic.NegativeNormalForm
