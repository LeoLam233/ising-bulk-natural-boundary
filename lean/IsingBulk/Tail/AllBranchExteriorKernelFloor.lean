import IsingBulk.Tail.MicrocoreDensity
import IsingBulk.Tail.CoareaRectangleKernel

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped BigOperators

theorem allBranchExterior_exp_phase_denominator (z : ℂ) :
    phaseDenominator (Real.exp z.re) z.im=‖1-Complex.exp z‖ := by
  unfold phaseDenominator
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 3
  have hh := Complex.re_add_im z
  simpa only [mul_comm] using hh

theorem allBranchExterior_exp_kernel_floor (z : ℂ) {a : ℝ} (ha : 0 < a)
    (hz : ‖Complex.exp z‖ ≤ Real.exp (-a)) :
    ‖1-Complex.exp z‖⁻¹ ≤ 2*(phaseDenominator (Real.exp (-a)) z.im)⁻¹ := by
  rw [← allBranchExterior_exp_phase_denominator]
  exact simple_kernel_radius_floor (Real.exp_pos _).le
    (by simpa only [Complex.norm_exp] using hz) (Real.exp_lt_one_iff.mpr (by linarith))

def allBranchExteriorYExponent {N : ℕ} (v θ : ℝ) (u : Fin N → ℝ) : ℂ :=
  (((N:ℝ)*v:ℝ):ℂ)+Complex.I*((∑ i, u i)-(N:ℝ)*θ:ℝ)

theorem allBranchExterior_regularY_exponent {n : ℕ} (v θ : ℝ) (s : ℂ)
    (u : Fin (n+1) → ℝ) (hg : ∀ i, 0 < (angularG v θ (u i:ℂ)).re) :
    regularYProduct s (chartMap v θ s u)=Complex.exp (allBranchExteriorYExponent v θ u) := by
  unfold regularYProduct
  simp only [chartMap,regularY_chartPhase _ _ _ _ (hg _),angularY]
  rw [← Complex.exp_sum]
  congr 1
  unfold allBranchExteriorYExponent
  simp only [sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  rw [← Finset.sum_mul]
  ring

theorem allBranchExterior_regular_kernel_floor {n : ℕ} (v θ : ℝ) (s : ℂ)
    (u : Fin (n+1) → ℝ) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (u i:ℂ)).re)
    {a : ℝ} (ha : 0 < a)
    (hz : ‖regularZProduct s (chartMap v θ s u)‖ ≤ Real.exp (-a)) :
    ‖regularKernel s (chartMap v θ s u)‖⁻¹ ≤
      4*twoPhaseKernel (-v) a ((∑ i, u i)-(n+1:ℝ)*θ,∑ i, (chartMap v θ s u i).re) := by
  have hY : ‖Complex.exp (allBranchExteriorYExponent v θ u)‖ ≤ Real.exp v := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [allBranchExteriorYExponent,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hy := allBranchExterior_exp_kernel_floor (allBranchExteriorYExponent v θ u)
    (show 0 < -v by linarith) (by simpa using hY)
  have hz' := allBranchExterior_exp_kernel_floor
    (-Complex.I*∑ i, chartMap v θ s u i) ha hz
  have hiZ : (-Complex.I*∑ i, chartMap v θ s u i).im=-(∑ i, (chartMap v θ s u i).re) := by
    simp [Complex.mul_im]
  have hiY : (allBranchExteriorYExponent v θ u).im=(∑ i, u i)-(n+1:ℝ)*θ := by
    simp [allBranchExteriorYExponent]
  rw [hiZ,phaseDenominator_neg] at hz'
  rw [hiY] at hy
  have hh := mul_le_mul hz' hy (inv_nonneg.mpr (norm_nonneg _)) (by
    unfold phaseDenominator
    positivity)
  rw [regularKernel,norm_mul,mul_inv_rev,allBranchExterior_regularY_exponent v θ s u hg]
  change ‖1-Complex.exp (-Complex.I*∑ i, chartMap v θ s u i)‖⁻¹ *
    ‖1-Complex.exp (allBranchExteriorYExponent v θ u)‖⁻¹ ≤ _
  apply hh.trans_eq
  unfold twoPhaseKernel
  dsimp only
  ring

theorem two_polar_kernel_floor (Y Z : ℂ) (F G a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hY : ‖Y‖ ≤ Real.exp (-a)) (hZ : ‖Z‖ ≤ Real.exp (-b))
    (hYpolar : Y=(‖Y‖:ℂ)*Complex.exp (Complex.I*(F:ℂ)))
    (hZpolar : Z=(‖Z‖:ℂ)*Complex.exp (-Complex.I*(G:ℂ))) :
    ‖(1-Y)*(1-Z)‖⁻¹ ≤ 4*twoPhaseKernel a b (F,G) := by
  have hy := simple_kernel_radius_floor (norm_nonneg Y) hY (Real.exp_lt_one_iff.mpr (by linarith : -a < 0))
    (t := F)
  have hz := simple_kernel_radius_floor (norm_nonneg Z) hZ (Real.exp_lt_one_iff.mpr (by linarith : -b < 0))
    (t := -G)
  have heY : phaseDenominator ‖Y‖ F=‖1-Y‖ := by unfold phaseDenominator; rw [← hYpolar]
  have heZ : phaseDenominator ‖Z‖ (-G)=‖1-Z‖ := by
    unfold phaseDenominator
    rw [Complex.ofReal_neg,mul_neg,← neg_mul,← hZpolar]
  rw [heY] at hy
  rw [heZ,phaseDenominator_neg] at hz
  have hh := mul_le_mul hy hz (inv_nonneg.mpr (norm_nonneg _)) (by unfold phaseDenominator; positivity)
  rw [norm_mul,mul_inv_rev]
  unfold twoPhaseKernel
  convert! hh using 1 <;> ring

theorem two_polar_cayley_kernel_floor (Y Z : ℂ) (F G a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hY : ‖Y‖ ≤ Real.exp (-a)) (hZ : ‖Z‖ ≤ Real.exp (-b))
    (hYpolar : Y=(‖Y‖:ℂ)*Complex.exp (Complex.I*(F:ℂ)))
    (hZpolar : Z=(‖Z‖:ℂ)*Complex.exp (-Complex.I*(G:ℂ))) :
    ‖((1+Y)/(1-Y))*((1+Z)/(1-Z))‖ ≤ 16*twoPhaseKernel a b (F,G) := by
  have hy1 : ‖Y‖ ≤ 1 := hY.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hz1 : ‖Z‖ ≤ 1 := hZ.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hy : ‖1+Y‖ ≤ 2 := by have hh := norm_add_le (1:ℂ) Y; norm_num at hh; linarith
  have hz : ‖1+Z‖ ≤ 2 := by have hh := norm_add_le (1:ℂ) Z; norm_num at hh; linarith
  have hp := two_polar_kernel_floor Y Z F G a b ha hb hY hZ hYpolar hZpolar
  rw [div_mul_div_comm,norm_div,norm_mul]
  calc
    _ ≤ 4/‖(1-Y)*(1-Z)‖ := div_le_div_of_nonneg_right
      (by nlinarith [norm_nonneg (1+Y),norm_nonneg (1+Z)]) (norm_nonneg _)
    _ ≤ 4*(4*twoPhaseKernel a b (F,G)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end
end IsingBulk.Tail
