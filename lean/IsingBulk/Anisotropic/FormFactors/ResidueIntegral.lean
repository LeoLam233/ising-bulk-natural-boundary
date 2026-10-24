import IsingBulk.Anisotropic.FormFactors.ResidueAlgebra

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First Set
open scoped BigOperators

theorem latticeClearedNumerator_differentiableAt {N : ℕ} {lam r : ℝ} {z : ℂ}
    {y u : Fin N → ℂ} (hr : r < 1) (hS : spectralS z ≠ 0) (hy : ∀ i,y i ≠ 0)
    (hu : ∀ i,‖u i‖ < r) (v : ℤ × ℤ) {x : Fin N → ℂ} (hx : x ∈ closedPolydisk N r) :
    DifferentiableAt ℂ (fun x => latticeClearedNumerator lam z y u x v) x := by
  have hxn (i) : ‖x i‖ < 1 := (hx i).trans_lt hr
  have hP := pairProduct_differentiableAt x hxn
  have hX := coordinateProduct_differentiableAt x
  have hD : DifferentiableAt ℂ (fun x : Fin N → ℂ =>
      ∏ i, 2*u i/(spectralS z*y i*(1-x i*u i))) x := by
    apply finite_product_differentiableAt
    intro i _
    have hi : DifferentiableAt ℂ (fun x : Fin N → ℂ => x i) x := differentiableAt_apply i x
    have hd := ((hi.mul_const (u i)).const_sub 1).const_mul (spectralS z*y i)
    have hn := mul_ne_zero (mul_ne_zero hS (hy i))
      (one_sub_mul_ne_zero_of_norm_lt_one (hxn i) ((hu i).trans hr))
    convert! (hd.inv hn).const_mul (2*u i) using 1
  exact (((hP.mul_const _).mul hD).mul (hX.pow _)).mul_const _

/-- Cauchy evaluation of every actual full-lattice coefficient's inner
contour, with the anisotropic S scale and both coordinate powers retained. -/
theorem lattice_residue_inner_integral (N : ℕ) {lam r : ℝ} {z : ℂ}
    (hr0 : 0 < r) (hr : r < 1) {y u : Fin N → ℂ}
    (hS : spectralS z ≠ 0) (hy : ∀ i,y i ≠ 0)
    (hu0 : ∀ i,u i ≠ 0) (hu : ∀ i,‖u i‖ < r)
    (he : ∀ i,RootEquation lam z (y i) (u i)) (v : ℤ × ℤ) :
    multiCircleIntegral r N (fun x => onsiteDensity lam z x y *
      (coordinateProduct x)^v.1.natAbs*(coordinateProduct y)^v.2.natAbs) =
    latticeClearedNumerator lam z y u u v := by
  calc
    _ = multiCircleIntegral r N (fun x =>
        (∏ i,(x i-u i)⁻¹)*latticeClearedNumerator lam z y u x v) := by
      apply multiCircleIntegral_congr hr0.le N
      intro x hx
      exact latticeDensity_eq_cauchy (fun i => norm_ne_zero_iff.mp ((hx i).trans_ne hr0.ne')) hu0 he v
    _ = _ := multiCircleIntegral_cauchy hr0 N _ u hu
      (fun x hx => latticeClearedNumerator_differentiableAt hr hS hy hu v hx)
end
end IsingBulk.Anisotropic.FormFactors
