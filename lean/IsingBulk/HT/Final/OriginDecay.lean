import IsingBulk.HT.Final.ExteriorFullSeries
import Mathlib.Analysis.Complex.RemovableSingularity

/-! A literal O(1/t) estimate for the complete odd source sum near infinity.
This supplies the removable high-temperature origin without a physical or
analytic-extension certificate. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology BigOperators

theorem standardDensity_quarter_norm_bound_of_resolvent_product {N : ℕ} (hN : 0 < N)
    (t : ℂ) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖=(1/4:ℝ)) (hy : ∀ i, ‖y i‖=(1/4:ℝ))
    {B : ℝ}
    (hres : ‖∏ i, (dispersion (x i) (y i) t)⁻¹‖ ≤ B) :
    ‖standardDensity t x y‖ ≤ (16*(16:ℝ)^N)*B := by
  have hpow : 1 ≤ (4:ℝ)^N := one_le_pow₀ (by norm_num)
  have hnx : ‖1+(coordinateProduct x)⁻¹‖ ≤ 2*(4:ℝ)^N := by
    have h := norm_add_le (1:ℂ) (coordinateProduct x)⁻¹
    rw [norm_one,coordinateProduct_quarter_inv_norm x hx] at h
    linarith
  have hny : ‖1+(coordinateProduct y)⁻¹‖ ≤ 2*(4:ℝ)^N := by
    have h := norm_add_le (1:ℂ) (coordinateProduct y)⁻¹
    rw [norm_one,coordinateProduct_quarter_inv_norm y hy] at h
    linarith
  have hdx := one_sub_coordinateProduct_quarter_norm_lower hN x hx
  have hdy := one_sub_coordinateProduct_quarter_norm_lower hN y hy
  have hden : (1/4:ℝ) ≤ ‖(1-coordinateProduct x)*(1-coordinateProduct y)‖ := by
    rw [norm_mul]
    nlinarith
  have hnum : ‖(1+(coordinateProduct x)⁻¹)*(1+(coordinateProduct y)⁻¹)‖ ≤
      4*(16:ℝ)^N := by
    rw [norm_mul]
    calc
      _ ≤ (2*(4:ℝ)^N)*(2*(4:ℝ)^N) := mul_le_mul hnx hny (norm_nonneg _) (by positivity)
      _ = _ := by rw [show (16:ℝ)=4*4 by norm_num,mul_pow]; ring
  have hglobal : ‖(1+(coordinateProduct x)⁻¹)*(1+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct x)*(1-coordinateProduct y))‖ ≤ 16*(16:ℝ)^N := by
    rw [norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖(1-coordinateProduct x)*(1-coordinateProduct y)‖)).mpr
    nlinarith [pow_pos (by norm_num : (0:ℝ)<16) N]
  have hpx := pairProduct_quarter_norm_le_one x hx
  have hpy := pairProduct_quarter_norm_le_one y hy
  have hc : ‖commonDensity t x y‖ ≤ B := by
    simp only [commonDensity,norm_mul]
    calc
      _ ≤ 1*1*B := mul_le_mul (mul_le_mul hpx hpy (norm_nonneg _) (by norm_num))
        hres (norm_nonneg _) (by norm_num)
      _ = B := by ring
  rw [standardDensity,norm_mul]
  calc
    _ ≤ (16*(16:ℝ)^N)*B := mul_le_mul hglobal hc (norm_nonneg _) (by positivity)
    _ = _ := rfl


theorem farExterior_dispersion_half_norm {s x y : ℂ} (hs : 16 < ‖s‖)
    (hx : (1/4:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 1)
    (hy : (1/4:ℝ) ≤ ‖y‖ ∧ ‖y‖ ≤ 1) : ‖s‖/2 ≤ ‖dispersion x y s‖ := by
  have hX := farExterior_half_trace_norm hx
  have hY := farExterior_half_trace_norm hy
  have hi : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (by linarith : 0 < ‖s‖)).mpr (by linarith)
  have he : s = dispersion x y s+(x+x⁻¹)/2+(y+y⁻¹)/2-s⁻¹ := by
    unfold dispersion sourceS
    ring
  have hb : ‖s‖ ≤ ‖dispersion x y s‖+‖(x+x⁻¹)/2‖+‖(y+y⁻¹)/2‖+‖s⁻¹‖ := by
    conv_lhs => rw [he]
    have h₁ := norm_sub_le
      (dispersion x y s+(x+x⁻¹)/2+(y+y⁻¹)/2) s⁻¹
    have h₂ := norm_add_le (dispersion x y s+(x+x⁻¹)/2) ((y+y⁻¹)/2)
    have h₃ := norm_add_le (dispersion x y s) ((x+x⁻¹)/2)
    linarith
  linarith

theorem quarter_resolvent_product_decay (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 16 < ‖s‖) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖=(1/4:ℝ)) (hy : ∀ i, ‖y i‖=(1/4:ℝ)) :
    ‖∏ i, (dispersion (x i) (y i) s)⁻¹‖ ≤ 2/‖s‖ := by
  let i₀ : Fin N := ⟨0,hN⟩
  have hD (i : Fin N) : 1 ≤ ‖dispersion (x i) (y i) s‖ :=
    farExterior_dispersion_norm_lower hs (by rw [hx i]; norm_num) (by rw [hy i]; norm_num)
  have hhalf := farExterior_dispersion_half_norm hs
    (x := x i₀) (y := y i₀) (by rw [hx i₀]; norm_num) (by rw [hy i₀]; norm_num)
  have h₀ : ‖(dispersion (x i₀) (y i₀) s)⁻¹‖ ≤ 2/‖s‖ := by
    rw [norm_inv]
    have hh := inv_anti₀ (by linarith : 0 < ‖s‖/2) hhalf
    simpa only [inv_div] using hh
  have hrest : ∏ i ∈ (Finset.univ.erase i₀), ‖(dispersion (x i) (y i) s)⁻¹‖ ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _; exact norm_nonneg _
    · intro i _; rw [norm_inv]; exact inv_le_one_of_one_le₀ (hD i)
  rw [norm_prod,← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  exact (mul_le_mul_of_nonneg_left hrest (norm_nonneg _)).trans (by simpa using h₀)

theorem standardFormFactor_quarter_decay (N : ℕ) (hN : 0 < N)
    {s : ℂ} (hs : 16 < ‖s‖) :
    ‖standardFormFactor N (1/4) s‖ ≤ (2/‖s‖)*(16/(N.factorial:ℝ)) := by
  have hb := multiCircleIntegral_norm_le N (r := 1/4) (by norm_num)
    (fun y => multiCircleIntegral (1/4) N (fun x => standardDensity s x y)) (by
      intro y hy
      apply multiCircleIntegral_norm_le N (by norm_num)
      intro x hx
      exact standardDensity_quarter_norm_bound_of_resolvent_product hN s x y hx hy
        (quarter_resolvent_product_decay N hN hs x y hx hy))
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Nat.cast_nonneg N.factorial))
  have he : (1/4:ℝ)^N*((1/4:ℝ)^N*((16*(16:ℝ)^N)*(2/‖s‖)))=16*(2/‖s‖) := by
    calc
      _ = (16*(((1/4:ℝ)*(1/4)*16)^N))*(2/‖s‖) := by simp only [mul_pow]; ring
      _ = _ := by norm_num
  rw [he] at hh
  simpa only [standardFormFactor,norm_mul,norm_inv,Complex.norm_natCast,
    div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh

def originMajorant : ℝ := 2 * ∑' n : ℕ, 16/((2*n+1).factorial:ℝ)

theorem exteriorOddSeries_scaled_bound {s : ℂ} (hs : 16 < ‖s‖) :
    ‖s*exteriorOddSeries s‖ ≤ originMajorant := by
  rw [exteriorOddSeries_eq_quarter_far hs,norm_mul]
  have hsum := fixedOddFullSeries_quarter_summable hs
  have hnorm := norm_tsum_le_tsum_norm hsum.norm
  have hdom (n : ℕ) : ‖oddFullCoefficient n (1/4) s‖ ≤
      (2/‖s‖)*(16/((2*n+1).factorial:ℝ)) :=
    standardFormFactor_quarter_decay _ (by omega) hs
  have hb := Summable.tsum_le_tsum hdom hsum.norm
    (quarter_oddFull_majorant_summable.mul_left (2/‖s‖))
  rw [tsum_mul_left] at hb
  have hs0 : ‖s‖ ≠ 0 := by linarith
  calc
    _ ≤ ‖s‖*((2/‖s‖)*∑' n : ℕ, 16/((2*n+1).factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hb) (norm_nonneg _)
    _ = originMajorant := by unfold originMajorant; field_simp

end
end IsingBulk.HT.Final
