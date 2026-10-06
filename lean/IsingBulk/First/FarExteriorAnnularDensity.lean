import IsingBulk.First.AnnularDensity

/-! Genuine norm-domain pole exclusion and source annular holomorphy near
infinity. These results serve only the exterior symmetry germ. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem farExterior_half_trace_norm {x : ℂ}
    (hx : (1/4:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 1) : ‖(x+x⁻¹)/2‖ ≤ 5/2 := by
  have hp : 0 < ‖x‖ := by linarith [hx.1]
  have hi : ‖x⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have hh := (inv_le_inv₀ hp (by norm_num : (0:ℝ)<1/4)).mpr hx.1
    norm_num at hh
    exact hh
  calc
    ‖(x+x⁻¹)/2‖ = ‖x+x⁻¹‖/2 := by rw [norm_div]; norm_num
    _ ≤ 5/2 := by have hh := norm_add_le x x⁻¹; linarith [hx.2]

theorem farExterior_sourceS_norm {s : ℂ} (hs : 16 < ‖s‖) : 15 < ‖sourceS s‖ := by
  have hi : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (by linarith : 0 < ‖s‖)).mpr (by linarith)
  have he : s = sourceS s-s⁻¹ := by unfold sourceS; ring
  have hh : ‖s‖ ≤ ‖sourceS s‖+‖s⁻¹‖ := by
    conv_lhs => rw [he]
    exact norm_sub_le _ _
  linarith

theorem farExterior_dispersion_norm_lower {s x y : ℂ} (hs : 16 < ‖s‖)
    (hx : (1/4:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 1)
    (hy : (1/4:ℝ) ≤ ‖y‖ ∧ ‖y‖ ≤ 1) : 1 ≤ ‖dispersion x y s‖ := by
  have hS := farExterior_sourceS_norm hs
  have hX := farExterior_half_trace_norm hx
  have hY := farExterior_half_trace_norm hy
  have he : sourceS s = dispersion x y s+(x+x⁻¹)/2+(y+y⁻¹)/2 := by
    unfold dispersion
    ring
  have hh : ‖sourceS s‖ ≤ ‖dispersion x y s‖+‖(x+x⁻¹)/2‖+‖(y+y⁻¹)/2‖ := by
    conv_lhs => rw [he]
    have h1 := norm_add_le (dispersion x y s + (x+x⁻¹)/2) ((y+y⁻¹)/2)
    have h2 := norm_add_le (dispersion x y s) ((x+x⁻¹)/2)
    linarith
  linarith

theorem farExterior_dispersion_ne_zero {s x y : ℂ} (hs : 16 < ‖s‖)
    (hx : (1/4:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 1)
    (hy : (1/4:ℝ) ≤ ‖y‖ ∧ ‖y‖ ≤ 1) : dispersion x y s ≠ 0 := by
  have hh := farExterior_dispersion_norm_lower hs hx hy
  exact norm_pos_iff.mp (by linarith)

theorem farExterior_doubleDensity_differentiableAt_maps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : 0 < N) {r R : ℝ} (hr : (1/4:ℝ) ≤ r) (hR : R < 1) {s : ℂ}
    (hs : 16 < ‖s‖)
    (x y : E → (Fin N → ℂ)) (p : E) (hx : DifferentiableAt ℂ x p) (hy : DifferentiableAt ℂ y p)
    (hxb : x p ∈ annularProduct N r R) (hyb : y p ∈ annularProduct N r R) :
    DifferentiableAt ℂ (fun q => doubleDensity s (x q) (y q)) p := by
  have hxn : ∀ i, ‖x p i‖ < 1 := fun i => (hxb i).2.trans_lt hR
  have hyn : ∀ i, ‖y p i‖ < 1 := fun i => (hyb i).2.trans_lt hR
  have hx0 : ∀ i, x p i ≠ 0 := fun i => norm_pos_iff.mp ((show 0 < r by linarith).trans_le (hxb i).1)
  have hy0 : ∀ i, y p i ≠ 0 := fun i => norm_pos_iff.mp ((show 0 < r by linarith).trans_le (hyb i).1)
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
    have hd0 : dispersion (x p i) (y p i) s ≠ 0 :=
      farExterior_dispersion_ne_zero hs ⟨hr.trans (hxb i).1, (hxn i).le⟩
        ⟨hr.trans (hyb i).1, (hyn i).le⟩
    exact hd.inv hd0
  have hnum := (hX.inv hX0).add (hY.inv hY0)
  have hden := (hX.const_sub 1).mul (hY.const_sub 1)
  have hglob : DifferentiableAt ℂ (fun q =>
      ((coordinateProduct (x q))⁻¹+(coordinateProduct (y q))⁻¹)/
      ((1-coordinateProduct (x q))*(1-coordinateProduct (y q)))) p := by
    convert! hnum.mul (hden.inv (mul_ne_zero hX1 hY1)) using 1
  exact hglob.mul ((hPX.mul hPY).mul hDs)

/-- Instantiation for an actual x-coordinate annulus, with y held fixed. -/
theorem farExterior_doubleDensity_x_annular (N : ℕ) (hN : 0 < N) {r R : ℝ} (hr : (1/4:ℝ) ≤ r) (hR : R < 1)
    {s : ℂ} (hs : 16 < ‖s‖)
    (y : Fin N → ℂ) (hy : y ∈ annularProduct N r R) :
    ∀ x ∈ annularProduct N r R, DifferentiableAt ℂ (fun x => doubleDensity s x y) x := by
  intro x hx
  exact farExterior_doubleDensity_differentiableAt_maps hN hr hR hs id (fun _ => y) x
    differentiableAt_id (differentiableAt_const y) hx hy

end
end IsingBulk.First
