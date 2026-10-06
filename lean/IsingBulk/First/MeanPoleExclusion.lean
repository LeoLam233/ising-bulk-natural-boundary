import IsingBulk.First.MeanPole
import IsingBulk.Analysis.BranchRadial
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Actual pole exclusion under downward mean motion. The local angular and
real-part restrictions remain explicit geometric hypotheses to be constructed
uniformly for the selected chart. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch

/-- The same exponential lower-sheet root as the source phase representation. -/
def phaseRoot (W : ℂ) : ℂ := Complex.exp (-Complex.I * lowerArccos W)

theorem phaseRoot_eq_inverse (W : ℂ) : phaseRoot W = (inverseCosineRoot W)⁻¹ := by
  unfold phaseRoot lowerArccos
  rw [show -Complex.I * (-Complex.I * Complex.log (inverseCosineRoot W)) =
    -Complex.log (inverseCosineRoot W) by ring_nf; simp [Complex.I_sq]]
  rw [Complex.exp_neg, Complex.exp_log (inverseCosineRoot_ne_zero W)]

theorem phaseRoot_ne_zero (W : ℂ) : phaseRoot W ≠ 0 := Complex.exp_ne_zero _

theorem phaseRoot_trace (W : ℂ) : phaseRoot W + (phaseRoot W)⁻¹ = 2*W := by
  rw [phaseRoot_eq_inverse, inv_inv, add_comm]
  exact inverseCosineRoot_trace W

theorem phaseRoot_norm_lt_one (W : ℂ) (hr : 0 < W.re) (hi : 0 < W.im) :
    ‖phaseRoot W‖ < 1 := by
  rw [phaseRoot_eq_inverse, norm_inv]
  exact inv_lt_one_of_one_lt₀ (inverseCosineRoot_norm W hr hi)

/-- Exact nonlinear monotonicity of the imaginary dispersion along a
vertical logarithmic-radius line at a lower angle. -/
theorem polar_dispersion_im_monotone (s : ℂ) (rho rho' angle : ℝ)
    (hrho : rho ≤ rho') (ha : Real.sin angle ≤ 0) :
    (Branch.dispersion s (Complex.exp ((rho:ℂ)+(angle:ℂ)*Complex.I))).im ≤
    (Branch.dispersion s (Complex.exp ((rho':ℂ)+(angle:ℂ)*Complex.I))).im := by
  rw [polar_dispersion_im, polar_dispersion_im]
  have h := mul_le_mul_of_nonpos_right (Real.sinh_le_sinh.mpr hrho) ha
  linarith

/-- Positivity on the top line persists throughout the downward deformation,
because the actual logarithmic radius increases. -/
theorem downward_dispersion_im_pos (s : ℂ) (rho angle depth N : ℝ)
    (hN : 0 < N) (hd : 0 ≤ depth) (ha : Real.sin angle ≤ 0)
    (htop : 0 < (Branch.dispersion s
      (Complex.exp ((rho:ℂ)+(angle:ℂ)*Complex.I))).im) :
    0 < (Branch.dispersion s
      (Complex.exp (((rho+depth/N:ℝ):ℂ)+(angle:ℂ)*Complex.I))).im := by
  exact htop.trans_le (polar_dispersion_im_monotone s rho (rho+depth/N) angle
    (le_add_of_nonneg_right (div_nonneg hd hN.le)) ha)

/-- No source Z product pole exists when all actual scalar roots stay on
the strict interior sheet. -/
theorem product_phaseRoot_ne_one {n : ℕ} (W : Fin (n+1) → ℂ)
    (hr : ∀ j, 0 < (W j).re) (hi : ∀ j, 0 < (W j).im) :
    coordinateProduct (fun j => phaseRoot (W j)) ≠ 1 := by
  have hp : ∏ j, ‖phaseRoot (W j)‖ < 1 := by
    have h := Finset.prod_lt_prod_of_nonempty₀
      (s := Finset.univ) (f := fun j => ‖phaseRoot (W j)‖) (g := fun _ => (1:ℝ))
      (fun j _ => norm_pos_iff.mpr (phaseRoot_ne_zero _))
      (fun j _ => phaseRoot_norm_lt_one _ (hr j) (hi j)) Finset.univ_nonempty
    simpa using h
  intro he
  have hh := congrArg norm he
  simp only [coordinateProduct, norm_prod, norm_one] at hh
  linarith

theorem phaseRoot_pair_denominator_ne_zero (W V : ℂ)
    (hWr : 0 < W.re) (hWi : 0 < W.im) (hVr : 0 < V.re) (hVi : 0 < V.im) :
    1-phaseRoot W*phaseRoot V ≠ 0 := by
  have hW := phaseRoot_norm_lt_one W hWr hWi
  have hV := phaseRoot_norm_lt_one V hVr hVi
  have hp : ‖phaseRoot W*phaseRoot V‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (phaseRoot W), norm_nonneg (phaseRoot V)]
  intro h
  have he : phaseRoot W*phaseRoot V = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hp
  exact lt_irrefl _ hp

end
end IsingBulk.First
