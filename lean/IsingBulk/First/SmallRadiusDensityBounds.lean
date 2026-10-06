import IsingBulk.First.ResidueBounds

/-! Elementary bounds for the actual offsite density on the fixed quarter-radius
contours. The contraction of each actual pair prevents growth quadratic in N. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- A genuine pair contraction at the fixed small radius. -/
theorem pairKernel_quarter_norm_le {x y : ℂ}
    (hx : ‖x‖ = (1/4:ℝ)) (hy : ‖y‖ = (1/4:ℝ)) :
    ‖pairKernel x y‖ ≤ (8/15:ℝ) := by
  have hn : ‖x-y‖ ≤ (1/2:ℝ) := by
    calc
      ‖x-y‖ ≤ ‖x‖+‖y‖ := norm_sub_le x y
      _ = (1/2:ℝ) := by rw [hx, hy]; norm_num
  have hd : (15/16:ℝ) ≤ ‖1-x*y‖ := by
    have h := norm_sub_norm_le (1:ℂ) (x*y)
    rw [norm_one, norm_mul, hx, hy] at h
    linarith
  rw [pairKernel, norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖1-x*y‖)).mpr
  nlinarith

theorem pairProduct_quarter_norm_le_one {N : ℕ} (x : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = (1/4:ℝ)) : ‖pairProduct x‖ ≤ 1 := by
  unfold pairProduct
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro i _
    positivity
  · intro i _
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro j _
      exact norm_nonneg _
    · intro j _
      exact (pairKernel_quarter_norm_le (hx i) (hx j)).trans (by norm_num)

theorem coordinateProduct_quarter_norm {N : ℕ} (x : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = (1/4:ℝ)) :
    ‖coordinateProduct x‖ = (1/4:ℝ)^N := by
  simp only [coordinateProduct, norm_prod, hx, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem coordinateProduct_quarter_inv_norm {N : ℕ} (x : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = (1/4:ℝ)) :
    ‖(coordinateProduct x)⁻¹‖ = (4:ℝ)^N := by
  rw [norm_inv, coordinateProduct_quarter_norm x hx, ← inv_pow]
  norm_num

theorem coordinateProduct_quarter_norm_le {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = (1/4:ℝ)) :
    ‖coordinateProduct x‖ ≤ (1/4:ℝ) := by
  cases N with
  | zero => omega
  | succ n =>
    rw [coordinateProduct_quarter_norm x hx, pow_succ]
    have h : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith

theorem one_sub_coordinateProduct_quarter_norm_lower {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = (1/4:ℝ)) :
    (1/2:ℝ) ≤ ‖1-coordinateProduct x‖ := by
  have h := norm_sub_norm_le (1:ℂ) (coordinateProduct x)
  rw [norm_one] at h
  have hX := coordinateProduct_quarter_norm_le hN x hx
  linarith

/-- The literal density bound follows from actual dispersion separation; the
far-exterior specialization below supplies that separation independently. -/
theorem doubleDensity_quarter_norm_bound_of_dispersion {N : ℕ} (hN : 0 < N)
    (s : ℂ) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = (1/4:ℝ)) (hy : ∀ i, ‖y i‖ = (1/4:ℝ))
    (hD : ∀ i, 1 ≤ ‖dispersion (x i) (y i) s‖) :
    ‖doubleDensity s x y‖ ≤ 8*(4:ℝ)^N := by
  have hPX := pairProduct_quarter_norm_le_one x hx
  have hPY := pairProduct_quarter_norm_le_one y hy
  have hDX := one_sub_coordinateProduct_quarter_norm_lower hN x hx
  have hDY := one_sub_coordinateProduct_quarter_norm_lower hN y hy
  have hnum : ‖(coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹‖ ≤ 2*(4:ℝ)^N := by
    calc
      _ ≤ ‖(coordinateProduct x)⁻¹‖+‖(coordinateProduct y)⁻¹‖ := norm_add_le _ _
      _ = _ := by rw [coordinateProduct_quarter_inv_norm x hx,
        coordinateProduct_quarter_inv_norm y hy]; ring
  have hden : (1/4:ℝ) ≤ ‖(1-coordinateProduct x)*(1-coordinateProduct y)‖ := by
    rw [norm_mul]
    nlinarith
  have hglob : ‖((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct x)*(1-coordinateProduct y))‖ ≤ 8*(4:ℝ)^N := by
    rw [norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖(1-coordinateProduct x)*(1-coordinateProduct y)‖)).mpr
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 4) N]
  have hres : ‖∏ i, (dispersion (x i) (y i) s)⁻¹‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro i _
      exact norm_nonneg _
    · intro i _
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (hD i)
  have hcommon : ‖commonDensity s x y‖ ≤ 1 := by
    simp only [commonDensity, norm_mul]
    calc
      _ ≤ 1*1*1 := mul_le_mul (mul_le_mul hPX hPY (norm_nonneg _) (by norm_num))
        hres (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  change ‖(((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)/
    ((1-coordinateProduct x)*(1-coordinateProduct y)))*commonDensity s x y‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (8*(4:ℝ)^N)*1 := mul_le_mul hglob hcommon (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

end
end IsingBulk.First
