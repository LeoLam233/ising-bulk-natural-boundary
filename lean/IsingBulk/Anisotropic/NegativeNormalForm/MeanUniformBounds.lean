import IsingBulk.Anisotropic.NegativeNormalForm.MeanCoefficients

/-! Dimension-independent bounds for the actual reciprocal-root mean field
and rank-one correction. No complex quadratic form occurs in a denominator. -/
noncomputable section
open scoped BigOperators
namespace IsingBulk.Anisotropic.NegativeNormalForm

 theorem norm_pairing_le_sup {n : ℕ} (v w : Config n) :
    ‖pairing v w‖≤(n:ℝ)*‖v‖*‖w‖ := by
  calc
    _ ≤ ∑ i : Fin n, ‖v i*w i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖*‖w‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm w i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

 theorem one_le_norm_one_add_sqrt (z : ℂ) : 1≤‖1+Complex.sqrt z‖ := by
  have hs : 0≤(Complex.sqrt z).re := by
    change 0≤(z^(2⁻¹:ℂ)).re
    rw [Complex.cpow_inv_two_re]
    positivity
  have h := Complex.re_le_norm (1+Complex.sqrt z)
  simp only [Complex.add_re,Complex.one_re] at h
  linarith

 theorem rankOneCoefficient_norm_le {n : ℕ} (ell : Config n) :
    ‖rankOneCoefficient ell‖≤(n:ℝ) := by
  simp only [rankOneCoefficient,norm_div,Complex.norm_natCast]
  exact div_le_self (Nat.cast_nonneg n) (one_le_norm_one_add_sqrt _)

 theorem meanCorrection_error_norm {n : ℕ} (ell w : Config n) :
    ‖meanCorrection ell w-w‖≤((n:ℝ)*‖ell‖)^2*‖w‖ := by
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro i
  change ‖w i+rankOneCoefficient ell*pairing w ell*ell i-w i‖≤_
  rw [add_sub_cancel_left,norm_mul,norm_mul]
  calc
    _ ≤ (n:ℝ)*((n:ℝ)*‖w‖*‖ell‖)*‖ell‖ := by
      gcongr
      · exact rankOneCoefficient_norm_le ell
      · exact norm_pairing_le_sup w ell
      · exact norm_le_pi_norm ell i
    _ = _ := by ring

 theorem reciprocal_sum_norm_lower {n : ℕ} (S : Config n) (δ : ℝ)
    (hS : ∀ i, ‖1-(S i)⁻¹‖≤δ) :
    (n:ℝ)*(1-δ)≤‖∑ i, (S i)⁻¹‖ := by
  have he : (∑ i, (S i)⁻¹)-(n:ℂ)=∑ i, ((S i)⁻¹-1) := by simp [Finset.sum_sub_distrib]
  have hb : ‖(∑ i, (S i)⁻¹)-(n:ℂ)‖≤(n:ℝ)*δ := by
    rw [he]
    calc
      _ ≤ ∑ i : Fin n, ‖(S i)⁻¹-1‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => by simpa only [norm_sub_rev] using hS i
      _ = _ := by simp
  have ht : (n:ℝ)≤‖∑ i, (S i)⁻¹‖+‖(∑ i, (S i)⁻¹)-(n:ℂ)‖ := by
    calc
      _ = ‖(∑ i, (S i)⁻¹)-((∑ i, (S i)⁻¹)-(n:ℂ))‖ := by rw [sub_sub_cancel]; simp
      _ ≤ _ := norm_sub_le _ _
  nlinarith

 theorem meanCoefficients_norm_le {n : ℕ} (hn : n ≠ 0) (S : Config n) (δ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ<1) (hS : ∀ i, ‖1-(S i)⁻¹‖≤δ) :
    ‖meanCoefficients S‖≤2*δ/((n:ℝ)*(1-δ)) := by
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdpos : 0<(n:ℝ)*(1-δ) := mul_pos hnpos (sub_pos.mpr hδ1)
  have hden := reciprocal_sum_norm_lower S δ hS
  have hcoord : ‖(fun i => (1-(S i)⁻¹)/(∑ j, (S j)⁻¹))‖≤δ/((n:ℝ)*(1-δ)) := by
    apply pi_norm_le_iff_of_nonneg (div_nonneg hδ hdpos.le) |>.mpr
    intro i
    rw [norm_div]
    exact (div_le_div_of_nonneg_right (hS i) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hδ hdpos hden)
  calc
    _ ≤ 2*‖(fun i => (1-(S i)⁻¹)/(∑ j, (S j)⁻¹))‖ := norm_project_le hn _
    _ ≤ 2*(δ/((n:ℝ)*(1-δ))) := mul_le_mul_of_nonneg_left hcoord (by norm_num)
    _ = _ := by ring

 theorem meanCorrection_reciprocal_error {n : ℕ} (hn : n ≠ 0) (S w : Config n) (δ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ<1) (hS : ∀ i, ‖1-(S i)⁻¹‖≤δ) :
    ‖meanCorrection (meanCoefficients S) w-w‖≤(2*δ/(1-δ))^2*‖w‖ := by
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hb : (n:ℝ)*‖meanCoefficients S‖≤2*δ/(1-δ) := by
    have h := mul_le_mul_of_nonneg_left (meanCoefficients_norm_le hn S δ hδ hδ1 hS) hnpos.le
    convert h using 1
    field_simp
  apply (meanCorrection_error_norm (meanCoefficients S) w).trans
  gcongr

end IsingBulk.Anisotropic.NegativeNormalForm
