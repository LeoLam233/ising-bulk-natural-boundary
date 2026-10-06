import IsingBulk.First.ActualLeadingDensity
import IsingBulk.First.MeanRadialPhase
import IsingBulk.First.ShapeArithmetic

/-! Values at the actual physical chart center, before any asymptotic limit. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators

@[simp] theorem shapeExtend_zero_exact {K : Type*} [AddCommGroup K] (n : ℕ) :
    shapeExtend (0 : Fin n → K) = 0 := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

@[simp] theorem shapeY_zero_exact (n : ℕ) (alpha : ℝ) (j : Fin (n+1)) :
    shapeY alpha (0 : Fin n → ℝ) j = exp (-(alpha:ℂ)*I) := by
  simp [shapeY]

theorem sourceW_density_center (a : OrderedChartData) :
    sourceW (exp ((a.theta:ℂ)*I)) (exp (-(a.alpha:ℂ)*I)) = (Real.cos a.beta:ℂ) := by
  have ht := IsingBulk.PrimeFamily.exp_angle_add_inv a.theta
  have ha := IsingBulk.PrimeFamily.exp_angle_add_inv (-a.alpha)
  simp only [Real.cos_neg, ofReal_neg] at ha
  have har : (Real.cos a.alpha:ℂ)+(Real.cos a.beta:ℂ)=2*(Real.cos a.theta:ℂ) := by
    exact_mod_cast a.angle_relation
  unfold sourceW sourceS
  rw [ht, ha]
  linear_combination -har

@[simp] theorem shapeZ_density_center (a : OrderedChartData) (n : ℕ) (j : Fin (n+1)) :
    shapeZ (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) j =
      exp (-(a.beta:ℂ)*I) := by
  unfold shapeZ
  rw [shapeY_zero_exact, sourceW_density_center, phaseRoot,
    lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])]
  congr 1
  ring

theorem one_sub_negative_angle_sq (beta : ℝ) :
    1-(exp (-(beta:ℂ)*I))^2 = 2*I*(Real.sin beta:ℂ)*exp (-(beta:ℂ)*I) := by
  have he : exp ((beta:ℂ)*I)*exp (-(beta:ℂ)*I) = 1 := by
    rw [← exp_add]
    simp
  have hd : exp ((beta:ℂ)*I)-exp (-(beta:ℂ)*I) = 2*I*(Real.sin beta:ℂ) := by
    simp only [exp_mul_I, cos_neg, sin_neg, ← ofReal_sin]
    ring
  have hm := congrArg (fun z : ℂ => z*exp (-(beta:ℂ)*I)) hd
  rw [sub_mul, he] at hm
  linear_combination hm

theorem one_sub_negative_angle_sq_ne_zero {beta : ℝ} (hb : Real.sin beta ≠ 0) :
    1-(exp (-(beta:ℂ)*I))^2 ≠ 0 := by
  rw [one_sub_negative_angle_sq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
    (ofReal_ne_zero.mpr hb)) (exp_ne_zero _)

theorem negative_angle_pair_value (beta : ℝ) :
    exp (-(beta:ℂ)*I)*exp (-(beta:ℂ)*I) /
      (1-exp (-(beta:ℂ)*I)*exp (-(beta:ℂ)*I))^2 =
        1 / (2*I*(Real.sin beta:ℂ))^2 := by
  rw [← pow_two, one_sub_negative_angle_sq, mul_pow]
  field_simp

theorem negative_angle_residue_value (beta : ℝ) :
    residueFactor (exp (-(beta:ℂ)*I)) = exp (-(beta:ℂ)*I)/(I*(Real.sin beta:ℂ)) := by
  unfold residueFactor
  rw [one_sub_negative_angle_sq]
  field_simp

theorem negative_angle_pow {N : ℕ} {beta : ℝ}
    (h : exp (-(N:ℂ)*(beta:ℂ)*I) = 1) :
    exp (-(beta:ℂ)*I)^N = 1 := by
  rw [← exp_nat_mul]
  convert h using 1
  congr 1
  ring

/-- The center value of the literal canceled numerator, with all phase and
measure factors retained before the final even-particle simplification. -/
theorem actualRegularFactor_center_explicit (a : OrderedChartData) (n : ℕ)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualRegularFactor (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) =
      2 * (2 ^ (2*(firstStrictPairs (n+1)).card) : ℂ)⁻¹ *
        ((I*(Real.sin a.beta:ℂ))^(2*(firstStrictPairs (n+1)).card+(n+1)))⁻¹ *
        ((2*(Real.pi:ℂ))^(n+1))⁻¹ := by
  have hy : exp (-(a.alpha:ℂ)*I)^(n+1) = 1 := negative_angle_pow (by simpa using ha)
  have hz : exp (-(a.beta:ℂ)*I)^(n+1) = 1 := negative_angle_pow (by simpa using hb)
  have hp : shapeZProduct (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) = 1 := by
    simpa [shapeZProduct, coordinateProduct] using hz
  unfold actualRegularFactor
  simp only [hp, inv_one, shapeZ_density_center, shapeY_zero_exact,
    negative_angle_pair_value, negative_angle_residue_value,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, hy, hz]
  rw [pow_add]
  simp only [one_div, mul_pow, ← pow_mul, mul_inv_rev]
  ring

/-- The actual coefficient is the displayed K, including the N! normalization;
the equality is derived from the physical numerator rather than postulated. -/
theorem actualRegularFactor_center_eq_K (a : OrderedChartData) (n : ℕ)
    (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualRegularFactor (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) /
      ((n+1).factorial:ℂ) = (a.K (n+1):ℂ) := by
  rw [actualRegularFactor_center_explicit a n ha hb, firstStrictPairs_twice_card]
  have hex : (n+1)*n+(n+1) = (n+1)^2 := by ring
  rw [hex, mul_pow]
  have hi : I^((n+1)^2) = 1 := by
    obtain ⟨p,hp⟩ := he
    rw [hp, show (p+p)^2 = 4*(p^2) by ring, pow_mul, I_pow_four, one_pow]
  rw [hi, one_mul]
  simp only [OrderedChartData.K, ofReal_mul, ofReal_div, ofReal_ofNat,
    ofReal_inv, ofReal_pow, ofReal_natCast]
  simp only [Nat.add_sub_cancel]
  ring

end
end IsingBulk.First
