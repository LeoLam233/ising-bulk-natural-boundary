import IsingBulk.First.DoubleContourFubini
import IsingBulk.First.ResidueAdmissibility

/-! Genuine continuity/integrability of the onsite and full-site source densities. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem commonDensity_continuous_angles (N : ℕ) (r : ℝ) (s : ℂ) (z : ℂ → ℂ)
    (h : ScalarResidueAdmissible r s z) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      commonDensity s (angleTuple r p.1) (angleTuple r p.2)) := by
  let x : ((Fin N → ℝ) × (Fin N → ℝ)) → Fin N → ℂ := fun p => angleTuple r p.1
  let y : ((Fin N → ℝ) × (Fin N → ℝ)) → Fin N → ℂ := fun p => angleTuple r p.2
  have hx : Continuous x := (angleTuple_continuous (N := N) r).comp continuous_fst
  have hy : Continuous y := (angleTuple_continuous (N := N) r).comp continuous_snd
  have hxn : ∀ p i, ‖x p i‖=r := fun _p _i => anglePoint_norm h.radius_pos.le _
  have hyn : ∀ p i, ‖y p i‖=r := fun _p _i => anglePoint_norm h.radius_pos.le _
  have hx0 : ∀ p i, x p i ≠ 0 := by
    intro p i he
    have hh := hxn p i
    simp [he] at hh
    linarith [h.radius_pos]
  have hy0 : ∀ p i, y p i ≠ 0 := by
    intro p i he
    have hh := hyn p i
    simp [he] at hh
    linarith [h.radius_pos]
  have hD : Continuous (fun p => ∏ i, (dispersion (x p i) (y p i) s)⁻¹) := by
    apply continuous_finsetProd
    intro i _
    have hi := (continuous_apply i).comp hx
    have hj := (continuous_apply i).comp hy
    have hd : Continuous (fun p => dispersion (x p i) (y p i) s) := by
      unfold dispersion
      exact (continuous_const.sub ((hi.add (hi.inv₀ (fun p => hx0 p i))).div_const 2)).sub
        ((hj.add (hj.inv₀ (fun p => hy0 p i))).div_const 2)
    apply hd.inv₀
    intro p
    exact dispersion_ne_zero_on_circle (h.toTuple N (y p) (fun j => hyn p j)) (hxn p i) i
  have hPX := continuous_pairProduct x hx (fun p i => (hxn p i).trans_lt h.radius_lt_one)
  have hPY := continuous_pairProduct y hy (fun p i => (hyn p i).trans_lt h.radius_lt_one)
  exact (hPX.mul hPY).mul hD

/-- Both additional observables have their actual pole-free angular densities. -/
theorem normalizationDensities_continuous_angles (N : ℕ) (hN : 0 < N)
    (r : ℝ) (s : ℂ) (z : ℂ → ℂ) (h : ScalarResidueAdmissible r s z) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => onsiteDensity s (angleTuple r p.1) (angleTuple r p.2)) ∧
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => standardDensity s (angleTuple r p.1) (angleTuple r p.2)) := by
  let x : ((Fin N → ℝ) × (Fin N → ℝ)) → Fin N → ℂ := fun p => angleTuple r p.1
  let y : ((Fin N → ℝ) × (Fin N → ℝ)) → Fin N → ℂ := fun p => angleTuple r p.2
  have hx : Continuous x := (angleTuple_continuous (N := N) r).comp continuous_fst
  have hy : Continuous y := (angleTuple_continuous (N := N) r).comp continuous_snd
  have hxn : ∀ p i, ‖x p i‖=r := fun _p _i => anglePoint_norm h.radius_pos.le _
  have hyn : ∀ p i, ‖y p i‖=r := fun _p _i => anglePoint_norm h.radius_pos.le _
  have hx0 : ∀ p i, x p i ≠ 0 := by
    intro p i he
    have hh := hxn p i
    simp [he] at hh
    linarith [h.radius_pos]
  have hy0 : ∀ p i, y p i ≠ 0 := by
    intro p i he
    have hh := hyn p i
    simp [he] at hh
    linarith [h.radius_pos]
  have hX := continuous_coordinateProduct x hx
  have hY := continuous_coordinateProduct y hy
  have hX0 : ∀ p, coordinateProduct (x p) ≠ 0 := fun p => Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 p i)
  have hY0 : ∀ p, coordinateProduct (y p) ≠ 0 := fun p => Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 p i)
  have hX1 : ∀ p, 1-coordinateProduct (x p) ≠ 0 := fun p =>
    one_sub_coordinateProduct_ne_zero hN (fun i => (hxn p i).trans_lt h.radius_lt_one)
  have hY1 : ∀ p, 1-coordinateProduct (y p) ≠ 0 := fun p =>
    one_sub_coordinateProduct_ne_zero hN (fun i => (hyn p i).trans_lt h.radius_lt_one)
  have hC := commonDensity_continuous_angles N r s z h
  constructor
  · exact ((hX.mul hY).inv₀ (fun p => mul_ne_zero (hX0 p) (hY0 p))).mul hC
  · exact (((continuous_const.add (hX.inv₀ hX0)).mul
      (continuous_const.add (hY.inv₀ hY0))).div
      ((continuous_const.sub hX).mul (continuous_const.sub hY))
      (fun p => mul_ne_zero (hX1 p) (hY1 p))).mul hC

end
end IsingBulk.First
