import IsingBulk.First.MeanAngularIdentity
import IsingBulk.First.MeanShapeIntegral
import IsingBulk.First.PeriodicLiftIntegral
import IsingBulk.First.CompatibleYLocalization
import IsingBulk.First.MeanFullIntegral

/-! Exact conversion of the actual periodically localized reduced source
integral to its fixed real shape/mean chart. No chart change-of-variables or
factorial/measure normalization identity is an input. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped ContDiff

def shiftedRawMeanShapeWeight {n : ℕ} (alpha : ℝ)
    (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  rawMeanShapeWeight chi eta (fun j => x j+alpha)

theorem rawMeanShapeWeight_meanShape {n : ℕ} (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ)
    (v : ℝ) (t : Fin n → ℝ) : rawMeanShapeWeight chi eta (meanShapeChart v t) = chi t*eta v := by
  have hN : (n+1:ℝ) ≠ 0 := by positivity
  simp only [rawMeanShapeWeight,shapeCoordinates_meanShapeChart hN,
    meanCoordinate_meanShapeChart hN,shapeExtend_castSucc]

theorem fixedYChartWeight_eq_periodicizeBump {n : ℕ} (alpha : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ} {H delta : ℝ}
    (hsmall : H+delta ≤ 1/2)
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta) :
    fixedYChartWeight alpha chi eta =
      periodicizeBump (fun _ => -alpha) (shiftedRawMeanShapeWeight alpha chi eta) := by
  funext theta
  rw [fixedYChartWeight_eq_periodicization alpha hsmall hchi heta]
  unfold periodicizeBump shiftedRawMeanShapeWeight centeredWrap
  congr 1
  funext j
  simp only [sub_neg_eq_add]
  ring

/-- The actual localized reduced form factor, with the fixed shape weight
outside the mean integration and the original N! outside both integrations. -/
theorem weightedReducedFormFactor_meanShape_integral {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (hr1 : Real.exp rho < 1) (hm : (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im)
    (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ)
    (hchiSmooth : ContDiff ℝ ∞ chi) (hetaSmooth : ContDiff ℝ ∞ eta)
    {H delta : ℝ} (hR : 0 ≤ H+delta) (hsmall : H+delta ≤ 1/2)
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta) :
    weightedReducedFormFactor (n+1) (Real.exp rho) (globalRoot s) (fixedYChartWeight alpha chi eta) =
      ((n+1).factorial:ℂ)⁻¹ * ∫ t : Fin n → ℝ, (chi t:ℂ)*
        ∫ v : ℝ, (eta v:ℂ)*meanLocalDensity s rho alpha t (v:ℂ) := by
  let F : (Fin (n+1) → ℝ) → ℂ := sourceReducedAngularDensity (Real.exp rho) s
  let w := shiftedRawMeanShapeWeight alpha chi eta
  let c : Fin (n+1) → ℝ := fun _ => -alpha
  have hF : Continuous F := sourceReducedAngularDensity_continuous (n+1) (by omega)
    (Real.exp_pos rho) hr1 hm
  have hraw : ContDiff ℝ ∞ (rawMeanShapeWeight chi eta) :=
    rawMeanShapeWeight_contDiff hchiSmooth hetaSmooth
  have hw : ContDiff ℝ ∞ w := hraw.comp (by fun_prop)
  have hws : ∀ x, w x ≠ 0 → ∀ i, |x i-c i| ≤ 1/2 := by
    intro x hx i
    have hb := (rawMeanShapeWeight_support_bound hchi heta hx i).le.trans hsmall
    simpa only [c,sub_neg_eq_add] using hb
  rw [weightedReducedFormFactor_eq_box (n+1) (by omega) (Real.exp_pos rho) hr1 hm _
    (fixedYChartWeight_contDiff alpha hchiSmooth hetaSmooth).continuous,
    fixedYChartWeight_eq_periodicizeBump alpha hsmall hchi heta]
  change ((n+1).factorial:ℂ)⁻¹ * (∫ x in angleBox (n+1), (periodicizeBump c w x:ℂ)*F x) = _
  rw [periodicizeBump_integral (n+1) c w hw hws F hF
    (sourceReducedAngularDensity_periodic (n+1) (Real.exp rho) s)]
  congr 1
  let f : (Fin (n+1) → ℝ) → ℂ := fun u =>
    (rawMeanShapeWeight chi eta u:ℂ)*F (fun j => u j-alpha)
  have hfc : Continuous f := (Complex.continuous_ofReal.comp hraw.continuous).mul
    (hF.comp (by fun_prop))
  have hfcompact : HasCompactSupport f :=
    ((rawMeanShapeWeight_hasCompactSupport hR hchi heta).comp_left
      (by simp : ((0:ℝ):ℂ)=0)).mul_right
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfcompact
  have hshift : (∫ x : Fin (n+1) → ℝ, (w x:ℂ)*F x) = ∫ u, f u := by
    have hh := integral_add_right_eq_self (μ := volume) (fun x : Fin (n+1) → ℝ => (w x:ℂ)*F x) c
    symm
    convert! hh using 1
    congr 1
    funext u
    dsimp only [f,w,shiftedRawMeanShapeWeight,c,Pi.add_apply]
    simp only [neg_add_cancel_right]
    rfl
  rw [hshift,integral_meanShapeChart n f hfi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only [f,F]
  rw [rawMeanShapeWeight_meanShape,sourceReducedAngularDensity_meanShape]
  push_cast
  ring

end
end IsingBulk.First
