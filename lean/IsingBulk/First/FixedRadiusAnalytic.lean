import IsingBulk.First.AngularResolvent
import Mathlib.Analysis.Analytic.Constructions

/-! Genuine fixed-radius analyticity for a source density with a continuous
spatial amplitude. All complex dependence is the actual dispersion product. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def rationalDoubleContour (N : ℕ) (r : ℝ)
    (A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ) (s : ℂ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    multiCircleIntegral r N (fun x => A x y * ∏ i, (dispersion (x i) (y i) s)⁻¹))

theorem rationalDoubleContour_analyticAt (N : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => A (angleTuple r p.1) (angleTuple r p.2)))
    {s : ℂ} (hs : s ∈ dampingDomain r) : AnalyticAt ℂ (rationalDoubleContour N r A) s := by
  let w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ := fun p =>
    angleProductJacobian r p.2*angleProductJacobian r p.1*A (angleTuple r p.1) (angleTuple r p.2)
  have hJ := angleProductJacobian_continuous (N := N) r
  have hw : Continuous w := ((hJ.comp continuous_snd).mul (hJ.comp continuous_fst)).mul hA
  have ha := (analyticAt_const (𝕜 := ℂ) (x := s) (v := (N.factorial:ℂ)⁻¹)).mul
    (angularResolventIntegral_analyticAt N hr hr1 w hw hs)
  apply ha.congr
  filter_upwards [dampingDomain_mem_nhds hs] with t ht
  have hf : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)*
        ∏ i, (dispersion (angleTuple r p.1 i) (angleTuple r p.2 i) t)⁻¹) := by
    have hc := hA.mul (angularResolventProduct_continuous hr hr1 ht)
    change Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)*
        sourceResolventProduct (angularDispersionTrace r) t p) at hc
    simpa only [angularResolventProduct_eq] using hc
  unfold rationalDoubleContour
  rw [doubleCircleIntegral_eq_product N r _ hf]
  dsimp only [Pi.mul_apply]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  dsimp only [w]
  rw [angularResolventProduct_eq]
  ring

/-- Removing the actual nonzero resolvents at one admissible parameter proves
continuity of the spatial amplitude; no continuity premise about a quotient
integral or about a selected root is used. -/
theorem spatialAmplitude_continuous {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hs : s ∈ dampingDomain r)
    (A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hF : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)*sourceResolventProduct (angularDispersionTrace r) s p)) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => A (angleTuple r p.1) (angleTuple r p.2)) := by
  have hP : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      ∏ i, (sourceS s-angularDispersionTrace r i p)) := by
    apply continuous_finsetProd
    intro i _
    exact continuous_const.sub (angularDispersionTrace_continuous hr i)
  convert! hF.mul hP using 1
  funext p
  have hp0 : (∏ i, (sourceS s-angularDispersionTrace r i p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => angularDispersion_ne_zero hr hr1 hs p i)
  change _ = (A (angleTuple r p.1) (angleTuple r p.2)*
    (∏ i, (sourceS s-angularDispersionTrace r i p)⁻¹))*
    ∏ i, (sourceS s-angularDispersionTrace r i p)
  rw [Finset.prod_inv_distrib, mul_assoc, inv_mul_cancel₀ hp0, mul_one]

end
end IsingBulk.First
