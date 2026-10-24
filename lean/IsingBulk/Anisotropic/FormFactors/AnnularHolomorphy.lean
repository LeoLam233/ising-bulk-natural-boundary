import IsingBulk.Anisotropic.FormFactors.ContourAnnulus
import IsingBulk.First.AnnularDensity

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem fullDensity_differentiableAt_maps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : 0 < N) {r R lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) (hR : R < 1)
    (x y : E → (Fin N → ℂ)) (p : E) (hx : DifferentiableAt ℂ x p) (hy : DifferentiableAt ℂ y p)
    (hxb : x p ∈ annularProduct N r R) (hyb : y p ∈ annularProduct N r R) :
    DifferentiableAt ℂ (fun q => fullDensity lam z (x q) (y q)) p := by
  have hxn : ∀ i, ‖x p i‖ < 1 := fun i => (hxb i).2.trans_lt hR
  have hyn : ∀ i, ‖y p i‖ < 1 := fun i => (hyb i).2.trans_lt hR
  have hx0 : ∀ i, x p i ≠ 0 := fun i => norm_pos_iff.mp (h.1.trans_le (hxb i).1)
  have hy0 : ∀ i, y p i ≠ 0 := fun i => norm_pos_iff.mp (h.1.trans_le (hyb i).1)
  have hX0 : coordinateProduct (x p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 i)
  have hY0 : coordinateProduct (y p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)
  have hX1 := one_sub_coordinateProduct_ne_zero hN hxn
  have hY1 := one_sub_coordinateProduct_ne_zero hN hyn
  have hX : DifferentiableAt ℂ (fun q => coordinateProduct (x q)) p :=
    (coordinateProduct_differentiableAt (x p)).comp p hx
  have hY : DifferentiableAt ℂ (fun q => coordinateProduct (y q)) p :=
    (coordinateProduct_differentiableAt (y p)).comp p hy
  have hPX : DifferentiableAt ℂ (fun q => IsingBulk.First.pairProduct (x q)) p :=
    (pairProduct_differentiableAt (x p) hxn).comp p hx
  have hPY : DifferentiableAt ℂ (fun q => IsingBulk.First.pairProduct (y q)) p :=
    (pairProduct_differentiableAt (y p) hyn).comp p hy
  have hDs : DifferentiableAt ℂ (fun q => ∏ i, (sliceDispersion lam z (x q i) (y q i))⁻¹) p := by
    apply finite_product_differentiableAt_general
    intro i _
    have hprojx : DifferentiableAt ℂ (fun t : Fin N → ℂ => t i) (x p) := differentiableAt_apply i (x p)
    have hprojy : DifferentiableAt ℂ (fun t : Fin N → ℂ => t i) (y p) := differentiableAt_apply i (y p)
    have hxi : DifferentiableAt ℂ (fun q => x q i) p := by convert! hprojx.comp p hx using 1
    have hyi : DifferentiableAt ℂ (fun q => y q i) p := by convert! hprojy.comp p hy using 1
    have hd : DifferentiableAt ℂ (fun q => sliceDispersion lam z (x q i) (y q i)) p := by
      unfold sliceDispersion dispersionPolynomial
      exact ((differentiableAt_const _).sub
        ((differentiableAt_const _).mul (hxi.add (hxi.inv (hx0 i))))).sub
        ((differentiableAt_const _).mul (hyi.add (hyi.inv (hy0 i))))
    have hd0 : sliceDispersion lam z (x p i) (y p i) ≠ 0 :=
      h.2.2 _ _ (hxb i).1 (hxn i).le (hyb i).1 (hyn i).le
    exact hd.inv hd0
  have hnum := ((differentiableAt_const (1 : ℂ)).add hX).mul ((differentiableAt_const (1 : ℂ)).add hY)
  have hden := ((hX.mul hY).mul (hX.const_sub 1)).mul (hY.const_sub 1)
  have hglob := hnum.mul (hden.inv
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hX0 hY0) hX1) hY1))
  convert! hglob.mul ((hPX.mul hPY).mul hDs) using 1

end
end IsingBulk.Anisotropic.FormFactors
