import IsingBulk.First.MeanLocalDensity
import IsingBulk.First.ResidueAlgebra

/-! Identification of the physical exponential mean-chart root with the
interior dispersion root in the genuine residue-reduction theorem. -/
namespace IsingBulk.First
noncomputable section

theorem phaseRoot_quadratic (W : ℂ) : (phaseRoot W)^2-2*W*phaseRoot W+1=0 := by
  have ht := phaseRoot_trace W
  have hz := phaseRoot_ne_zero W
  have hm := congrArg (fun x : ℂ => phaseRoot W*x) ht
  simp only [mul_add, mul_inv_cancel₀ hz] at hm
  linear_combination hm

theorem phaseRoot_eq_interior_root {W z : ℂ}
    (hz : z^2-2*W*z+1=0) (hzn : ‖z‖ < 1) (hr : 0 < W.re) (hi : 0 < W.im) :
    phaseRoot W = z :=
  quadratic_root_unique (phaseRoot_quadratic W) hz (phaseRoot_norm_lt_one W hr hi) hzn

/-- The same tuple is used by residue reduction and by mean deformation;
there is no replacement of the physical branch by an unrelated local model. -/
theorem meanChartRoots_eq_admissible {n : ℕ} (s : ℂ) (rho alpha r : ℝ)
    (t : Fin n → ℝ) (v : ℂ) (z : Fin (n+1) → ℂ)
    (h : ResidueAdmissible r s (meanChartY rho alpha t v) z)
    (hr : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).re)
    (hi : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).im) :
    meanChartRoots s rho alpha t v = z := by
  funext j
  apply phaseRoot_eq_interior_root _ ((h.root_inside j).trans h.radius_lt_one) (hr j) (hi j)
  have hh := h.root_quadratic j
  unfold IsingBulk.Jets.chartW IsingBulk.Branch.dispersion
  unfold sourceS meanChartY at hh
  linear_combination hh

end
end IsingBulk.First
