import IsingBulk.First.RegularPhaseDomain
import IsingBulk.First.MeanLocalDomain

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

theorem product_phaseRoot_ne_one {n : ℕ} (W : Fin (n+1) → ℂ)
    (hi : ∀ j, 0 < (W j).im) :
    coordinateProduct (fun j => phaseRoot (W j)) ≠ 1 := by
  have hp : ∏ j, ‖phaseRoot (W j)‖ < 1 := by
    have h := Finset.prod_lt_prod_of_nonempty₀
      (s := Finset.univ) (f := fun j => ‖phaseRoot (W j)‖) (g := fun _ => (1:ℝ))
      (fun j _ => norm_pos_iff.mpr (phaseRoot_ne_zero _))
      (fun j _ => phaseRoot_norm_lt_one_of_upper (hi j)) Finset.univ_nonempty
    simpa using h
  intro he
  have hh := congrArg norm he
  simp only [coordinateProduct, norm_prod, norm_one] at hh
  linarith

theorem phaseRoot_pair_denominator_ne_zero (W V : ℂ)
    (hWi : 0 < W.im) (hVi : 0 < V.im) : 1-phaseRoot W*phaseRoot V ≠ 0 := by
  have hW := phaseRoot_norm_lt_one_of_upper hWi
  have hV := phaseRoot_norm_lt_one_of_upper hVi
  have hp : ‖phaseRoot W*phaseRoot V‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (phaseRoot W), norm_nonneg (phaseRoot V)]
  intro h
  have he : phaseRoot W*phaseRoot V = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hp
  exact lt_irrefl _ hp

private theorem scalar_product_differentiableAt {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f : ι → ℂ → ℂ) (v : ℂ)
    (hf : ∀ i ∈ t, DifferentiableAt ℂ (f i) v) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ t, f i w) v :=
  (HasFDerivAt.finsetProd (fun i hi => (hf i hi).hasFDerivAt)).differentiableAt

theorem meanChartRoots_differentiableAt {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (t : Fin n → ℝ) (j : Fin (n+1)) (v : ℂ)
    (hi : 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).im) :
    DifferentiableAt ℂ (fun w => meanChartRoots s rho alpha t w j) v := by
  have hu : DifferentiableAt ℂ (fun w : ℂ => ((shapeExtend t j:ℝ):ℂ)+w/(n+1)) v := by
    fun_prop
  have hW := (IsingBulk.Jets.chartW_angular s rho alpha
    (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).differentiableAt.comp v hu
  have hp := (IsingBulk.Branch.lowerArccos_analytic_of_upper hi).differentiableAt.comp v hW
  exact (hp.const_mul (-I)).cexp

private theorem pairProduct_along_differentiableAt {N : ℕ} (x : ℂ → Fin N → ℂ) (v : ℂ)
    (hx : ∀ i, DifferentiableAt ℂ (fun w => x w i) v)
    (hn : ∀ i j, i < j → 1-x v i*x v j ≠ 0) :
    DifferentiableAt ℂ (fun w => pairProduct (x w)) v := by
  unfold pairProduct
  apply scalar_product_differentiableAt
  intro i _
  apply scalar_product_differentiableAt
  intro j hj
  exact ((hx i).sub (hx j)).div (((hx i).mul (hx j)).const_sub 1)
    (hn i j (Finset.mem_filter.mp hj).2)

/-- The numerator regularity needed by the genuine residue theorem is proved
for the actual finite products, rather than passed through a conclusion record. -/
theorem meanLocalNumerator_differentiableAt {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (t : Fin n → ℝ) (v : ℂ)
    (hi : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).im)
    (hypair : ∀ i j, i < j → 1-meanChartY rho alpha t v i*meanChartY rho alpha t v j ≠ 0) :
    DifferentiableAt ℂ (meanLocalNumerator s rho alpha t) v := by
  let y := meanChartY rho alpha t
  let z := meanChartRoots s rho alpha t
  have hy : ∀ i, DifferentiableAt ℂ (fun w => y w i) v :=
    fun i => meanChartY_differentiableAt rho alpha t i v
  have hz : ∀ i, DifferentiableAt ℂ (fun w => z w i) v :=
    fun i => meanChartRoots_differentiableAt s rho alpha t i v (hi i)
  have hy0 (i) : y v i ≠ 0 := Complex.exp_ne_zero _
  have hz0 (i) : z v i ≠ 0 := phaseRoot_ne_zero _
  have hY : DifferentiableAt ℂ (fun w => coordinateProduct (y w)) v :=
    scalar_product_differentiableAt Finset.univ _ v (fun i _ => hy i)
  have hZ : DifferentiableAt ℂ (fun w => coordinateProduct (z w)) v :=
    scalar_product_differentiableAt Finset.univ _ v (fun i _ => hz i)
  have hY0 : coordinateProduct (y v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)
  have hZ0 : coordinateProduct (z v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)
  have hZ1 : 1-coordinateProduct (z v) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact Ne.symm (product_phaseRoot_ne_one _ hi)
  have hzpair (i j) : 1-z v i*z v j ≠ 0 :=
    phaseRoot_pair_denominator_ne_zero _ _ (hi i) (hi j)
  have hpz := pairProduct_along_differentiableAt z v hz (fun i j _ => hzpair i j)
  have hpy := pairProduct_along_differentiableAt y v hy hypair
  have hR : DifferentiableAt ℂ (fun w => ∏ i, residueFactor (z w i)) v := by
    apply scalar_product_differentiableAt
    intro i _
    have hden : 1-(z v i)^2 ≠ 0 := by simpa only [pow_two] using hzpair i i
    exact ((hz i).pow 2 |>.const_mul 2).div (((hz i).pow 2).const_sub 1) hden
  have hJ : DifferentiableAt ℂ (meanAngularJacobian rho alpha t) v :=
    scalar_product_differentiableAt Finset.univ _ v (fun i _ => (hy i).div_const _)
  exact (((((hZ.inv hZ0).add (hY.inv hY0)).div (hZ.const_sub 1) hZ1).mul hpz).mul hpy).mul hR |>.mul hJ


theorem meanChartY_pair_denominator_ne_zero {n : ℕ} (rho alpha : ℝ)
    (t : Fin n → ℝ) (v : ℂ)
    (ha : ∀ j, -Real.pi < (meanChartExponent rho alpha t v j).im ∧
      (meanChartExponent rho alpha t v j).im < 0) (i j : Fin (n+1)) :
    1-meanChartY rho alpha t v i*meanChartY rho alpha t v j ≠ 0 :=
  exp_pair_denominator_ne_zero_lower_strip (ha i) (ha j)

/-- All regularity assumptions of the actual contour theorem are discharged
from explicit pointwise geometric inequalities for its physical variables. -/
theorem meanLocalNumerator_shift_differentiableOn {n : ℕ} (s : ℂ)
    (rho alpha delta top bottom : ℝ) (t : Fin n → ℝ)
    (hi : ∀ w ∈ rectangleSet delta top bottom, ∀ j,
      0 < (IsingBulk.Jets.chartW s rho alpha
        (((shapeExtend t j:ℝ):ℂ)+(physicalMeanPole (n+1) rho+w)/(n+1))).im)
    (ha : ∀ w ∈ rectangleSet delta top bottom, ∀ j,
      -Real.pi < (meanChartExponent rho alpha t (physicalMeanPole (n+1) rho+w) j).im ∧
      (meanChartExponent rho alpha t (physicalMeanPole (n+1) rho+w) j).im < 0) :
    DifferentiableOn ℂ
      (fun w => meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho+w))
      (rectangleSet delta top bottom) := by
  intro w hw
  have hd := meanLocalNumerator_differentiableAt s rho alpha t
    (physicalMeanPole (n+1) rho+w) (hi w hw)
    (fun i j _ => meanChartY_pair_denominator_ne_zero rho alpha t
      (physicalMeanPole (n+1) rho+w) (ha w hw) i j)
  exact (hd.comp w (differentiableAt_id.const_add (physicalMeanPole (n+1) rho))).differentiableWithinAt


/-- The same tuple is used by residue reduction and by mean deformation;
there is no replacement of the physical branch by an unrelated local model. -/
theorem meanChartRoots_eq_admissible {n : ℕ} (s : ℂ) (rho alpha r : ℝ)
    (t : Fin n → ℝ) (v : ℂ) (z : Fin (n+1) → ℂ)
    (h : ResidueAdmissible r s (meanChartY rho alpha t v) z)
    (hi : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).im) :
    meanChartRoots s rho alpha t v = z := by
  funext j
  apply phaseRoot_eq_interior_root_of_upper _ ((h.root_inside j).trans h.radius_lt_one) (hi j)
  have hh := h.root_quadratic j
  unfold IsingBulk.Jets.chartW IsingBulk.Branch.dispersion
  unfold sourceS meanChartY at hh
  linear_combination hh

end
end IsingBulk.First.Regular
