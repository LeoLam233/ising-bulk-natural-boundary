import IsingBulk.Tail.MixedHybridChart
import IsingBulk.Tail.OriginalMicrocoreChart
import IsingBulk.Tail.MicrocoreDensityFactors

/-! The regular inverse chart agrees with the literal coupled contour on
lower angular arcs. No occupancy is replaced by an independent variable. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set
open scoped BigOperators

def mixedActualLogRadius {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) : ℝ :=
  Real.log r+lam*retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i

theorem mixed_actual_angularY {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    angularY (mixedActualLogRadius f r τ lam θ i) 0 (θ i:ℂ)=deformedPoint f r τ lam θ i := by
  rw [deformedPoint_polar f hr τ lam θ i]
  simp [angularY,mixedActualLogRadius]

theorem mixed_actual_chartPhase {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) :
    chartPhase s (mixedActualLogRadius f r τ lam θ i) 0 (θ i:ℂ)=mixedContourPhase f r τ lam s θ i := by
  unfold chartPhase chartW mixedContourPhase mixedSourcePhase
  rw [mixed_actual_angularY f hr τ lam θ i]
  rfl

theorem mixed_actual_angularG_positive {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) (hsin : Real.sin (θ i)<0) :
    0<(angularG (mixedActualLogRadius f r τ lam θ i) 0 (θ i:ℂ)).re := by
  rw [angularG_real_re]
  simp only [sub_zero]
  have hpos := add_pos (Real.exp_pos (mixedActualLogRadius f r τ lam θ i))
    (Real.exp_pos (-mixedActualLogRadius f r τ lam θ i))
  nlinarith [mul_neg_of_pos_of_neg hpos hsin]

theorem mixed_actual_regularY {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hsin : Real.sin (θ i)<0) :
    regularY s (mixedContourPhase f r τ lam s θ i)=deformedPoint f r τ lam θ i := by
  rw [← mixed_actual_chartPhase f hr τ lam s θ i,
    regularY_chartPhase s _ 0 _ (mixed_actual_angularG_positive f r τ lam θ i hsin),
    mixed_actual_angularY f hr τ lam θ i]

theorem mixed_actual_regularA {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hsin : Real.sin (θ i)<0) :
    regularA s (mixedContourPhase f r τ lam s θ i)=mixedSourceA s (deformedPoint f r τ lam θ i) := by
  unfold regularA regularG
  rw [mixed_actual_regularY f hr τ lam s θ i hsin]
  unfold mixedSourceA sourceSPrime
  congr 1
  ring

theorem mixed_actual_inverseSlope {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hsin : Real.sin (θ i)<0) :
    mixedInverseSlope s (mixedContourPhase f r τ lam s θ i)=
      (mixedSourceSlope s (deformedPoint f r τ lam θ i))⁻¹ := by
  unfold mixedInverseSlope regularG
  rw [mixed_actual_regularY f hr τ lam s θ i hsin]
  unfold mixedSourceSlope mixedContourPhase
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem mixed_actual_branch_measure_denominator {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (hsin : Real.sin (θ i)<0) :
    1-(deformedPoint f r τ lam θ i)^(-2:ℤ)≠0 := by
  let y := deformedPoint f r τ lam θ i
  have hy : y≠0 := deformedPoint_nonzero f hr.ne' τ lam θ i
  have hg : 0<(Complex.I*(y-y⁻¹)/2).re := by
    have h := mixed_actual_angularG_positive f r τ lam θ i hsin
    simpa only [angularG,mixed_actual_angularY f hr τ lam θ i] using h
  intro hd
  have hsquare : y^2=1 := inv_injective (by
    simpa only [zpow_neg,zpow_ofNat,inv_one] using (sub_eq_zero.mp hd).symm)
  have hz : y-y⁻¹=0 := by
    field_simp
    simpa only [mul_zero] using sub_eq_zero.mpr hsquare
  simp [hz] at hg

/-- The exact one-body measure is regular after the genuine branch
Jacobian is extracted, even when the coupled radial exponent is positive. -/
theorem mixed_actual_regular_onebody {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hsin : Real.sin (θ i)<0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedSourceSlope s (deformedPoint f r τ lam θ i)*
      microRegularOneBody s (mixedContourPhase f r τ lam s θ i) =
      residueFactor (globalRoot s (deformedPoint f r τ lam θ i))*deformedPoint f r τ lam θ i/(2*(Real.pi:ℂ)) := by
  have hh := micro_regular_onebody_source s (mixedActualLogRadius f r τ lam θ i) 0 (θ i:ℂ)
    (mixed_actual_angularG_positive f r τ lam θ i hsin)
    (by simpa only [mixed_actual_angularY f hr τ lam θ i] using
      mixed_actual_branch_measure_denominator f hr τ lam θ i hsin)
    (by simpa only [mixed_actual_chartPhase f hr τ lam s θ i,mixedContourPhase] using
      mixedSourcePhase_sin_ne hW)
  rw [mixed_actual_angularY f hr τ lam θ i,mixed_actual_chartPhase f hr τ lam s θ i] at hh
  convert hh using 1
  unfold mixedSourceSlope chartB angularG
  rw [mixed_actual_angularY f hr τ lam θ i,mixed_actual_chartPhase f hr τ lam s θ i]
  unfold mixedContourPhase
  ring

end
end IsingBulk.Tail
