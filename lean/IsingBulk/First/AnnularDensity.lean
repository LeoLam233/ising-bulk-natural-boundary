import IsingBulk.First.AnnulusProduct
import IsingBulk.First.MixedRadiusDamping

/-! Actual source-density holomorphy on mixed closed annular products.
All pole exclusions are derived from the source radius/parameter margin. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem finite_product_differentiableAt_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [DecidableEq ι] (t : Finset ι) (f : ι → E → ℂ) (p : E)
    (hf : ∀ i ∈ t, DifferentiableAt ℂ (f i) p) :
    DifferentiableAt ℂ (fun q => ∏ i ∈ t, f i q) p :=
  (HasFDerivAt.finsetProd (fun i hi => (hf i hi).hasFDerivAt)).differentiableAt

theorem doubleDensity_differentiableAt_maps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : 0 < N) {r R : ℝ} (hr : 0 < r) (hR : R < 1) {s : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im)
    (x y : E → (Fin N → ℂ)) (p : E) (hx : DifferentiableAt ℂ x p) (hy : DifferentiableAt ℂ y p)
    (hxb : x p ∈ annularProduct N r R) (hyb : y p ∈ annularProduct N r R) :
    DifferentiableAt ℂ (fun q => doubleDensity s (x q) (y q)) p := by
  have hxn : ∀ i, ‖x p i‖ < 1 := fun i => (hxb i).2.trans_lt hR
  have hyn : ∀ i, ‖y p i‖ < 1 := fun i => (hyb i).2.trans_lt hR
  have hx0 : ∀ i, x p i ≠ 0 := fun i => norm_pos_iff.mp (hr.trans_le (hxb i).1)
  have hy0 : ∀ i, y p i ≠ 0 := fun i => norm_pos_iff.mp (hr.trans_le (hyb i).1)
  have hX0 : coordinateProduct (x p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 i)
  have hY0 : coordinateProduct (y p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)
  have hX1 := one_sub_coordinateProduct_ne_zero hN hxn
  have hY1 := one_sub_coordinateProduct_ne_zero hN hyn
  have hX : DifferentiableAt ℂ (fun q => coordinateProduct (x q)) p :=
    (coordinateProduct_differentiableAt (x p)).comp p hx
  have hY : DifferentiableAt ℂ (fun q => coordinateProduct (y q)) p :=
    (coordinateProduct_differentiableAt (y p)).comp p hy
  have hPX : DifferentiableAt ℂ (fun q => pairProduct (x q)) p :=
    (pairProduct_differentiableAt (x p) hxn).comp p hx
  have hPY : DifferentiableAt ℂ (fun q => pairProduct (y q)) p :=
    (pairProduct_differentiableAt (y p) hyn).comp p hy
  have hDs : DifferentiableAt ℂ (fun q => ∏ i, (dispersion (x q i) (y q i) s)⁻¹) p := by
    apply finite_product_differentiableAt_general
    intro i _
    have hprojx : DifferentiableAt ℂ (fun t : Fin N → ℂ => t i) (x p) := differentiableAt_apply i (x p)
    have hprojy : DifferentiableAt ℂ (fun t : Fin N → ℂ => t i) (y p) := differentiableAt_apply i (y p)
    have hxi : DifferentiableAt ℂ (fun q => x q i) p := by convert! hprojx.comp p hx using 1
    have hyi : DifferentiableAt ℂ (fun q => y q i) p := by convert! hprojy.comp p hy using 1
    have hd : DifferentiableAt ℂ (fun q => dispersion (x q i) (y q i) s) p := by
      convert! ((differentiableAt_const (sourceS s)).sub
        ((hxi.add (hxi.inv (hx0 i))).mul_const (2:ℂ)⁻¹)).sub
          ((hyi.add (hyi.inv (hy0 i))).mul_const (2:ℂ)⁻¹) using 1
    have hd0 : dispersion (x p i) (y p i) s ≠ 0 := by
      have him := dispersion_im_positive_on_annulus hr (hxb i).1 (hyb i).1
        (hxn i).le (hyn i).le hmargin
      exact fun he => (ne_of_gt him) (congrArg Complex.im he)
    exact hd.inv hd0
  have hnum := (hX.inv hX0).add (hY.inv hY0)
  have hden := (hX.const_sub 1).mul (hY.const_sub 1)
  have hglob : DifferentiableAt ℂ (fun q =>
      ((coordinateProduct (x q))⁻¹+(coordinateProduct (y q))⁻¹)/
      ((1-coordinateProduct (x q))*(1-coordinateProduct (y q)))) p := by
    convert! hnum.mul (hden.inv (mul_ne_zero hX1 hY1)) using 1
  exact hglob.mul ((hPX.mul hPY).mul hDs)

/-- Instantiation for an actual x-coordinate annulus, with y held fixed. -/
theorem doubleDensity_x_annular (N : ℕ) (hN : 0 < N) {r R : ℝ} (hr : 0 < r) (hR : R < 1)
    {s : ℂ} (hmargin : r⁻¹-r < (sourceS s).im)
    (y : Fin N → ℂ) (hy : y ∈ annularProduct N r R) :
    ∀ x ∈ annularProduct N r R, DifferentiableAt ℂ (fun x => doubleDensity s x y) x := by
  intro x hx
  exact doubleDensity_differentiableAt_maps hN hr hR hmargin id (fun _ => y) x
    differentiableAt_id (differentiableAt_const y) hx hy

theorem doubleDensity_swap {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    doubleDensity s x y = doubleDensity s y x := by
  have hp : (∏ i, (dispersion (x i) (y i) s)⁻¹) = ∏ i, (dispersion (y i) (x i) s)⁻¹ := by
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    unfold dispersion
    ring
  unfold doubleDensity commonDensity
  rw [hp]
  ring

end
end IsingBulk.First
