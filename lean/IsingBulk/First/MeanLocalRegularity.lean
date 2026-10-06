import IsingBulk.First.MeanLocalDensity

/-! Differentiability of the literal residue numerator from explicit branch
quadrants and denominator conditions, with no assumed regularity conclusion. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators

private theorem scalar_product_differentiableAt {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f : ι → ℂ → ℂ) (v : ℂ)
    (hf : ∀ i ∈ t, DifferentiableAt ℂ (f i) v) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ t, f i w) v :=
  (HasFDerivAt.finsetProd (fun i hi => (hf i hi).hasFDerivAt)).differentiableAt

theorem meanChartY_differentiableAt {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ)
    (j : Fin (n+1)) (v : ℂ) :
    DifferentiableAt ℂ (fun w => meanChartY rho alpha t w j) v := by
  unfold meanChartY IsingBulk.Jets.angularY
  fun_prop

theorem meanChartRoots_differentiableAt {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (t : Fin n → ℝ) (j : Fin (n+1)) (v : ℂ)
    (hr : 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).re)
    (hi : 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).im) :
    DifferentiableAt ℂ (fun w => meanChartRoots s rho alpha t w j) v := by
  have hu : DifferentiableAt ℂ (fun w : ℂ => ((shapeExtend t j:ℝ):ℂ)+w/(n+1)) v := by
    fun_prop
  have hW := (IsingBulk.Jets.chartW_angular s rho alpha
    (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).differentiableAt.comp v hu
  have hp := (IsingBulk.Branch.lowerArccos_differentiable _ hr hi).comp v hW
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
    (hr : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).re)
    (hi : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).im)
    (hypair : ∀ i j, i < j → 1-meanChartY rho alpha t v i*meanChartY rho alpha t v j ≠ 0) :
    DifferentiableAt ℂ (meanLocalNumerator s rho alpha t) v := by
  let y := meanChartY rho alpha t
  let z := meanChartRoots s rho alpha t
  have hy : ∀ i, DifferentiableAt ℂ (fun w => y w i) v :=
    fun i => meanChartY_differentiableAt rho alpha t i v
  have hz : ∀ i, DifferentiableAt ℂ (fun w => z w i) v :=
    fun i => meanChartRoots_differentiableAt s rho alpha t i v (hr i) (hi i)
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
    exact Ne.symm (product_phaseRoot_ne_one _ hr hi)
  have hzpair (i j) : 1-z v i*z v j ≠ 0 :=
    phaseRoot_pair_denominator_ne_zero _ _ (hr i) (hi i) (hr j) (hi j)
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

end
end IsingBulk.First
