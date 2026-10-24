import IsingBulk.Anisotropic.NegativeDominance.QuantitativeOddMomentum

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

theorem edgeRoot_boundary_quadratic_gap {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im) :
    ∃ c : ℝ, 0<c ∧ ∀ q∈Icc (-Real.pi) Real.pi,
      c*q^2≤1-‖edgeRoot b B q‖ := by
  let M : ℝ := |b|+1+2*‖B‖
  let k : ℝ := 2*B.im/Real.pi^2
  have hM : 0<M := by dsimp [M]; positivity
  have hk : 0<k := by dsimp [k]; positivity
  refine ⟨k/(2*M+1),by positivity,?_⟩
  intro q hq
  by_cases hq0 : q=0
  · rw [hq0,pow_two,zero_mul,mul_zero]
    linarith [(edgeRoot_bounds hb hB 0).1]
  have hm : k*q^2≤(edgeW b B q).im := by
    have hh := edgeParamW_im_margin (B := fun _ => B) (u := (0 : ℂ)) b hB.le le_rfl (abs_le.mpr hq)
    simpa only [k,edgeParamW,edgeW,add_zero,Complex.zero_im,zero_add] using hh
  have hw : 0<(edgeW b B q).im := lt_of_lt_of_le (mul_pos hk (sq_pos_of_ne_zero hq0)) hm
  have hn : ‖edgeW b B q‖≤M := by
    have hh := edgeParamW_norm_bound (B := fun _ => B) (u := (0 : ℂ)) b (by simp) le_rfl q
    simpa only [M,edgeParamW,edgeW,add_zero] using hh
  have hgap := interiorRoot_modulus_gap hw hn
  rw [edgeRoot,continuedRoot_eq_interiorRoot hw]
  calc
    k/(2*M+1)*q^2 = (k*q^2)/(2*M+1) := by ring
    _ ≤ (edgeW b B q).im/(2*M+1) := div_le_div_of_nonneg_right hm (by positivity)
    _ ≤ _ := hgap

/-- A dimension-uniform polynomial resolvent gap for the entire actual odd
constrained torus, including the collision neighborhood. -/
theorem odd_negative_boundary_product_gap {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im) :
    ∃ c : ℝ, 0<c ∧ ∀ (n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ,
      c/((n+1 : ℕ) : ℝ)^2≤1-‖∏ i,edgeRoot b B (negativeShiftedAngles n v i)‖ := by
  obtain ⟨c,hc,hgap⟩ := edgeRoot_boundary_quadratic_gap hb hB
  refine ⟨4*c,by positivity,?_⟩
  intro n hn v
  let q := negativeShiftedAngles n v
  have hr (i : Fin (n+1)) : ‖edgeRoot b B (q i)‖≤1 := (edgeRoot_bounds hb hB _).1
  obtain ⟨i,hi⟩ := (IsGreatest.pi_norm q).1
  have hsq : (q i)^2=‖q‖^2 := by
    rw [←hi]
    change (q i)^2=‖q i‖^2
    simp only [Real.norm_eq_abs,sq_abs]
  have hg := hgap (q i) (wrapAngle_mem _)
  rw [hsq] at hg
  have hprod := root_product_norm_le_factor (fun i => edgeRoot b B (q i)) hr i
  have htotal : c*‖q‖^2≤1-‖∏ i,edgeRoot b B (q i)‖ := by linarith
  have hm := odd_shifted_angles_norm_lower hn v
  have hm2 : 4≤((n+1 : ℕ) : ℝ)^2*‖q‖^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) hm 2
    simpa only [mul_pow,show (2 : ℝ)^2=4 by norm_num] using hh
  have hN : 0<((n+1 : ℕ) : ℝ)^2 := by positivity
  apply (div_le_iff₀ hN).mpr
  have h1 := mul_le_mul_of_nonneg_left hm2 hc.le
  have h2 := mul_le_mul_of_nonneg_left htotal hN.le
  nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
