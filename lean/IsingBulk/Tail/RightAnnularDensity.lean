import IsingBulk.First.AnnularDensity

/-! The actual source density on right-trace annuli; all original normalized
objects are reused. Positive real dispersion replaces positive imaginary dispersion. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem right_dispersion_re_positive_on_annulus {r : ℝ} (hr : 0 < r) {x y s : ℂ}
    (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) (hx1 : ‖x‖ ≤ 1) (hy1 : ‖y‖ ≤ 1)
    (hs : 1+r⁻¹ < (sourceS s).re) : 0 < (dispersion x y s).re := by
  have hxre : x.re ≤ 1 := (Complex.re_le_norm x).trans hx1
  have hyre : y.re ≤ 1 := (Complex.re_le_norm y).trans hy1
  have hxinv : (x⁻¹).re ≤ r⁻¹ := by
    apply (Complex.re_le_norm (x⁻¹)).trans
    rw [norm_inv]
    exact inv_anti₀ hr hx
  have hyinv : (y⁻¹).re ≤ r⁻¹ := by
    apply (Complex.re_le_norm (y⁻¹)).trans
    rw [norm_inv]
    exact inv_anti₀ hr hy
  simp only [dispersion,Complex.sub_re,Complex.div_ofNat_re,Complex.add_re]
  linarith

theorem right_doubleDensity_differentiableAt_maps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : 0 < N) {r R : ℝ} (hr : 0 < r) (hR : R < 1) {s : ℂ}
    (hmargin : 1+r⁻¹ < (sourceS s).re)
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
      have him := right_dispersion_re_positive_on_annulus hr (hxb i).1 (hyb i).1
        (hxn i).le (hyn i).le hmargin
      exact fun he => (ne_of_gt him) (congrArg Complex.re he)
    exact hd.inv hd0
  have hnum := (hX.inv hX0).add (hY.inv hY0)
  have hden := (hX.const_sub 1).mul (hY.const_sub 1)
  have hglob : DifferentiableAt ℂ (fun q =>
      ((coordinateProduct (x q))⁻¹+(coordinateProduct (y q))⁻¹)/
      ((1-coordinateProduct (x q))*(1-coordinateProduct (y q)))) p := by
    convert! hnum.mul (hden.inv (mul_ne_zero hX1 hY1)) using 1
  exact hglob.mul ((hPX.mul hPY).mul hDs)

/-- Instantiation for an actual x-coordinate annulus, with y held fixed. -/
theorem right_doubleDensity_x_annular (N : ℕ) (hN : 0 < N) {r R : ℝ} (hr : 0 < r) (hR : R < 1)
    {s : ℂ} (hmargin : 1+r⁻¹ < (sourceS s).re)
    (y : Fin N → ℂ) (hy : y ∈ annularProduct N r R) :
    ∀ x ∈ annularProduct N r R, DifferentiableAt ℂ (fun x => doubleDensity s x y) x := by
  intro x hx
  exact right_doubleDensity_differentiableAt_maps hN hr hR hmargin id (fun _ => y) x
    differentiableAt_id (differentiableAt_const y) hx hy


end
end IsingBulk.Tail
