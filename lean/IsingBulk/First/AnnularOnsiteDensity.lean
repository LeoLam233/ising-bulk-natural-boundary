import IsingBulk.First.AnnularDensity

/-! Genuine onsite-density holomorphy on the same mixed closed annular product.
The missing global product denominators are not reintroduced. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem onsiteDensity_differentiableAt_maps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (_hN : 0 < N) {r R : ℝ} (hr : 0 < r) (hR : R < 1) {s : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im)
    (x y : E → (Fin N → ℂ)) (p : E) (hx : DifferentiableAt ℂ x p) (hy : DifferentiableAt ℂ y p)
    (hxb : x p ∈ annularProduct N r R) (hyb : y p ∈ annularProduct N r R) :
    DifferentiableAt ℂ (fun q => onsiteDensity s (x q) (y q)) p := by
  have hxn : ∀ i, ‖x p i‖ < 1 := fun i => (hxb i).2.trans_lt hR
  have hyn : ∀ i, ‖y p i‖ < 1 := fun i => (hyb i).2.trans_lt hR
  have hx0 : ∀ i, x p i ≠ 0 := fun i => norm_pos_iff.mp (hr.trans_le (hxb i).1)
  have hy0 : ∀ i, y p i ≠ 0 := fun i => norm_pos_iff.mp (hr.trans_le (hyb i).1)
  have hX0 : coordinateProduct (x p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 i)
  have hY0 : coordinateProduct (y p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)
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
  have hglob := (hX.mul hY).inv (mul_ne_zero hX0 hY0)
  exact hglob.mul ((hPX.mul hPY).mul hDs)

/-- Instantiation for an actual x-coordinate annulus, with y held fixed. -/
theorem onsiteDensity_x_annular (N : ℕ) (hN : 0 < N) {r R : ℝ} (hr : 0 < r) (hR : R < 1)
    {s : ℂ} (hmargin : r⁻¹-r < (sourceS s).im)
    (y : Fin N → ℂ) (hy : y ∈ annularProduct N r R) :
    ∀ x ∈ annularProduct N r R, DifferentiableAt ℂ (fun x => onsiteDensity s x y) x := by
  intro x hx
  exact onsiteDensity_differentiableAt_maps hN hr hR hmargin id (fun _ => y) x
    differentiableAt_id (differentiableAt_const y) hx hy

theorem onsiteDensity_swap {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    onsiteDensity s x y = onsiteDensity s y x := by
  have hp : (∏ i, (dispersion (x i) (y i) s)⁻¹) = ∏ i, (dispersion (y i) (x i) s)⁻¹ := by
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    unfold dispersion
    ring
  unfold onsiteDensity commonDensity
  rw [hp,mul_comm (coordinateProduct x) (coordinateProduct y)]
  ring

end
end IsingBulk.First
