import IsingBulk.Tail.SelectorLegality

/-! Holomorphicity at every legal real-homotopy parameter, using the
canceled density rather than uncanceled y-pair fractions. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators
set_option maxHeartbeats 800000

 theorem canceledPair_differentiableAt {s yi yj : ℂ} (hy : yi*yj ≠ 0)
    (z w : ℂ → ℂ) (hz : DifferentiableAt ℂ z s) (hw : DifferentiableAt ℂ w s)
    (hgap : 1-z s*w s ≠ 0) :
    DifferentiableAt ℂ (fun t => canceledPair yi yj (z t) (w t)) s := by
  unfold canceledPair
  exact (((differentiableAt_const (-(yi-yj)^2)).mul hz).mul hw).div
    ((differentiableAt_const (yi*yj)).mul (((differentiableAt_const (1:ℂ)).sub (hz.mul hw)).pow 2))
    (mul_ne_zero hy (pow_ne_zero 2 hgap))

 theorem canceledReducedDensity_differentiableAt {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℂ) (hy : ∀ i, y i ≠ 0) (hY : 1-coordinateProduct y ≠ 0)
    (z : ℂ → Fin N → ℂ) (s : ℂ)
    (hz : ∀ i, DifferentiableAt ℂ (fun t => z t i) s)
    (hz0 : ∀ i, z s i ≠ 0) (hzn : ∀ i, ‖z s i‖ < 1) :
    DifferentiableAt ℂ (fun t => canceledReducedDensity (z t) y) s := by
  have hZ : DifferentiableAt ℂ (fun t => coordinateProduct (z t)) s := by
    unfold coordinateProduct
    exact DifferentiableAt.fun_finsetProd (fun i _ => hz i)
  have hZ0 : coordinateProduct (z s) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)
  have hZ1 := one_sub_coordinateProduct_ne_zero hN hzn
  have hpair : DifferentiableAt ℂ (fun t => canceledPairProduct (z t) y) s := by
    unfold canceledPairProduct
    apply DifferentiableAt.fun_finsetProd
    intro i _
    apply DifferentiableAt.fun_finsetProd
    intro j _
    exact canceledPair_differentiableAt (mul_ne_zero (hy i) (hy j))
      (fun t => z t i) (fun t => z t j) (hz i) (hz j)
      (one_sub_mul_ne_zero_of_norm_lt_one (hzn i) (hzn j))
  have hres : DifferentiableAt ℂ (fun t => ∏ i, residueFactor (z t i)) s := by
    apply DifferentiableAt.fun_finsetProd
    intro i _
    unfold residueFactor
    exact ((differentiableAt_const (2:ℂ)).mul ((hz i).pow 2)).div
      ((differentiableAt_const (1:ℂ)).sub ((hz i).pow 2))
      (by simpa [pow_two] using one_sub_mul_ne_zero_of_norm_lt_one (hzn i) (hzn i))
  unfold canceledReducedDensity
  exact ((((hZ.inv hZ0).add_const ((coordinateProduct y)⁻¹)).div
    (((differentiableAt_const (1:ℂ)).sub hZ).mul_const (1-coordinateProduct y)) (mul_ne_zero hZ1 hY)).mul hpair).mul hres

 theorem deformedPoint_nonzero {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : r ≠ 0)
    (τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f r τ lam θ i ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)

 theorem pulledDensity_differentiableAt {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (θ : Fin N → ℝ) (s : ℂ) (hs : s ≠ 0)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) :
    DifferentiableAt ℂ (fun t => pulledDensity f r τ lam t θ) s := by
  have hy := deformedPoint_nonzero f hr.ne' τ lam θ
  have hY := homotopy_y_gap_nonzero hN f hr hr1 hτ hlam θ hp hm1
  have hW : ∀ i, 0 < (sourceW s (deformedPoint f r τ lam θ i)).im := by
    intro i
    exact (sourceW_upper_of_margin hr hr1 hmargin (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
      (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp hm0 hps hms i)
  have hd := canceledReducedDensity_differentiableAt hN (deformedPoint f r τ lam θ) hy hY
    (fun t i => globalRoot t (deformedPoint f r τ lam θ i)) s
    (fun i => globalRoot_parameter_differentiableAt hs (hW i))
    (fun i => globalRoot_nonzero s _) (fun i => interiorRoot_norm_lt_one (hW i))
  exact hd.const_mul _

end
end IsingBulk.Tail
