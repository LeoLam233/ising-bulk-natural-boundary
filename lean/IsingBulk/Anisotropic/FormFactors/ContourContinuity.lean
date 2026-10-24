import IsingBulk.Anisotropic.FormFactors.ContourAnnulus
import IsingBulk.HT.Contour.PhysicalLatticeSummation

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

theorem commonDensity_continuous_angles (N : ℕ) {r lam : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      commonDensity lam z (angleTuple r p.1) (angleTuple r p.2)) := by
  let x := fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r p.1
  let y := fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r p.2
  have hx : Continuous x := (angleTuple_continuous r).comp continuous_fst
  have hy : Continuous y := (angleTuple_continuous r).comp continuous_snd
  have hxn : ∀ p i, ‖x p i‖=r := fun _ _ => anglePoint_norm h.1.le _
  have hyn : ∀ p i, ‖y p i‖=r := fun _ _ => anglePoint_norm h.1.le _
  have hx0 : ∀ p i, x p i ≠ 0 := fun p i => norm_ne_zero_iff.mp ((hxn p i).trans_ne h.1.ne')
  have hy0 : ∀ p i, y p i ≠ 0 := fun p i => norm_ne_zero_iff.mp ((hyn p i).trans_ne h.1.ne')
  have hD : Continuous (fun p => ∏ i, (sliceDispersion lam z (x p i) (y p i))⁻¹) := by
    apply continuous_finsetProd
    intro i _
    have hi := (continuous_apply i).comp hx
    have hj := (continuous_apply i).comp hy
    have hd : Continuous (fun p => sliceDispersion lam z (x p i) (y p i)) := by
      unfold sliceDispersion dispersionPolynomial
      exact (continuous_const.sub (continuous_const.mul (hi.add (hi.inv₀ (fun p => hx0 p i))))).sub
        (continuous_const.mul (hj.add (hj.inv₀ (fun p => hy0 p i))))
    apply hd.inv₀
    intro p
    exact h.2.2 _ _ (hxn p i).ge ((hxn p i).le.trans h.2.1.le)
      (hyn p i).ge ((hyn p i).le.trans h.2.1.le)
  exact ((continuous_pairProduct x hx (fun p i => (hxn p i).trans_lt h.2.1)).mul
    (continuous_pairProduct y hy (fun p i => (hyn p i).trans_lt h.2.1))).mul hD

theorem normalizationDensities_continuous_angles (N : ℕ) (hN : 0 < N)
    {r lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      onsiteDensity lam z (angleTuple r p.1) (angleTuple r p.2)) ∧
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      fullDensity lam z (angleTuple r p.1) (angleTuple r p.2)) := by
  let x := fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r p.1
  let y := fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r p.2
  have hx : Continuous x := (angleTuple_continuous r).comp continuous_fst
  have hy : Continuous y := (angleTuple_continuous r).comp continuous_snd
  have hxn : ∀ p i, ‖x p i‖=r := fun _ _ => anglePoint_norm h.1.le _
  have hyn : ∀ p i, ‖y p i‖=r := fun _ _ => anglePoint_norm h.1.le _
  have hX := continuous_coordinateProduct x hx
  have hY := continuous_coordinateProduct y hy
  have hX0 : ∀ p, coordinateProduct (x p) ≠ 0 := fun p => Finset.prod_ne_zero_iff.mpr
    (fun i _ => norm_ne_zero_iff.mp ((hxn p i).trans_ne h.1.ne'))
  have hY0 : ∀ p, coordinateProduct (y p) ≠ 0 := fun p => Finset.prod_ne_zero_iff.mpr
    (fun i _ => norm_ne_zero_iff.mp ((hyn p i).trans_ne h.1.ne'))
  have hX1 : ∀ p, 1-coordinateProduct (x p) ≠ 0 := fun p =>
    one_sub_coordinateProduct_ne_zero hN (fun i => (hxn p i).trans_lt h.2.1)
  have hY1 : ∀ p, 1-coordinateProduct (y p) ≠ 0 := fun p =>
    one_sub_coordinateProduct_ne_zero hN (fun i => (hyn p i).trans_lt h.2.1)
  have hC := commonDensity_continuous_angles N h
  constructor
  · exact ((hX.mul hY).inv₀ (fun p => mul_ne_zero (hX0 p) (hY0 p))).mul hC
  · exact (((continuous_const.add hX).mul (continuous_const.add hY)).div
      (((hX.mul hY).mul (continuous_const.sub hX)).mul (continuous_const.sub hY))
      (fun p => mul_ne_zero (mul_ne_zero (mul_ne_zero (hX0 p) (hY0 p)) (hX1 p)) (hY1 p))).mul hC

/-- The exact full coefficient is an ordinary integral on the complete
2N-dimensional compact angle box, with its two Jacobians retained. -/
theorem unscaledFullCoefficientAtRadius_eq_box (N : ℕ) (hN : 0 < N)
    {r lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    unscaledFullCoefficientAtRadius N r lam z =
      (N.factorial:ℂ)⁻¹ * ∫ p in angleBox N ×ˢ angleBox N,
        doubleAngularDensityOf r (fullDensity lam z) p := by
  unfold unscaledFullCoefficientAtRadius
  rw [doubleCircleIntegral_eq_product N r _ (normalizationDensities_continuous_angles N hN h).2]
  rfl
end
end IsingBulk.Anisotropic.FormFactors
