import IsingBulk.First.ContourParameterDomain
import IsingBulk.First.QuarterContourBound
import IsingBulk.First.FarExteriorMixedContour

/-! The literal normalized form factors have an elementary geometric majorant
and genuine parameter holomorphy at the fixed radius one quarter near infinity. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem farExterior_doubleFormFactor_quarter_norm_bound (N : ℕ) (hN : 0 < N)
    {s : ℂ} (hs : 16 < ‖s‖) : ‖doubleFormFactor N (1/4) s‖ ≤ 8*(1/4:ℝ)^N := by
  apply doubleFormFactor_quarter_norm_bound_of_dispersion N hN s
  intro x hx y hy i
  apply farExterior_dispersion_norm_lower hs
  · rw [hx i]; norm_num
  · rw [hy i]; norm_num

theorem farExterior_angularDispersion_ne_zero {N : ℕ} {s : ℂ} (hs : 16 < ‖s‖)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) (i : Fin N) :
    sourceS s-angularDispersionTrace (1/4) i p ≠ 0 := by
  rw [sourceS_sub_angularDispersionTrace]
  apply farExterior_dispersion_ne_zero hs
  · change (1/4:ℝ) ≤ ‖anglePoint (1/4) (p.1 i)‖ ∧ ‖anglePoint (1/4) (p.1 i)‖ ≤ 1
    rw [anglePoint_norm (by norm_num)]; norm_num
  · change (1/4:ℝ) ≤ ‖anglePoint (1/4) (p.2 i)‖ ∧ ‖anglePoint (1/4) (p.2 i)‖ ≤ 1
    rw [anglePoint_norm (by norm_num)]; norm_num

theorem doubleFormFactor_quarter_analyticOn (N : ℕ) (hN : 0 < N) :
    AnalyticOnNhd ℂ (doubleFormFactor N (1/4)) {s : ℂ | 16 < ‖s‖} := by
  intro s hs
  let A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun x y =>
    ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct x)*(1-coordinateProduct y))*pairProduct x*pairProduct y
  have hfac : ∀ t x y, doubleDensity t x y = A x y*∏ i, (dispersion (x i) (y i) t)⁻¹ := by
    intro t x y
    dsimp only [A, doubleDensity, commonDensity]
    ring
  have hf := farExterior_mixedDoubleDensity_continuous N hN
    (r := 1/4) (R := 1/4) (rx := 1/4) (ry := 1/4)
    le_rfl (by norm_num) ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ hs
  have hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple (1/4) p.1) (angleTuple (1/4) p.2)) := by
    apply spatialAmplitude_continuous_of_no_poles (by norm_num) s
      (farExterior_angularDispersion_ne_zero hs) A
    simpa only [angularResolventProduct_eq, ← hfac] using hf
  have ha := rationalDoubleContour_analyticAt_on N (r := 1/4) (by norm_num) A hA
    (U := {t : ℂ | 16 < ‖t‖}) (isOpen_lt continuous_const continuous_norm)
    (fun t ht => norm_pos_iff.mp (by change 16 < ‖t‖ at ht; linarith))
    (fun _ ht => farExterior_angularDispersion_ne_zero ht) hs
  convert! ha using 1
  funext t
  simp only [doubleFormFactor, rationalDoubleContour, hfac]

end
end IsingBulk.First
