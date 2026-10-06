import IsingBulk.First.FixedRadiusAnalytic

/-! Parameter holomorphy on a genuine open source domain with no dispersion poles.
The radius is fixed and the full normalized contours are retained. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem rationalDoubleContour_analyticAt_on (N : ℕ) {r : ℝ} (hr : 0 < r)
    (A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)))
    {U : Set ℂ} (hU : IsOpen U) (h0 : ∀ t ∈ U, t ≠ 0)
    (hD : ∀ t ∈ U, ∀ p : (Fin N → ℝ) × (Fin N → ℝ), ∀ i,
      sourceS t-angularDispersionTrace r i p ≠ 0)
    {s : ℂ} (hs : s ∈ U) : AnalyticAt ℂ (rationalDoubleContour N r A) s := by
  let w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ := fun p =>
    angleProductJacobian r p.2*angleProductJacobian r p.1*
      A (angleTuple r p.1) (angleTuple r p.2)
  have hJ := angleProductJacobian_continuous (N := N) r
  have hw : Continuous w := ((hJ.comp continuous_snd).mul (hJ.comp continuous_fst)).mul hA
  have hi : AnalyticAt ℂ (fun t => ∫ p in angleBox N ×ˢ angleBox N,
      w p*sourceResolventProduct (angularDispersionTrace r) t p) s := by
    apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hs)
    intro t ht
    exact (resolventIntegral_differentiableAt (isCompact_Icc.prod isCompact_Icc)
      (angularDispersionTrace r) (angularDispersionTrace_continuous hr) w hw
      (hU.mem_nhds ht) h0 hD).differentiableWithinAt
  have ha := (analyticAt_const (𝕜 := ℂ) (x := s) (v := (N.factorial:ℂ)⁻¹)).mul hi
  apply ha.congr
  filter_upwards [hU.mem_nhds hs] with t ht
  have hP : Continuous (sourceResolventProduct (angularDispersionTrace (N := N) r) t) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_const.sub (angularDispersionTrace_continuous hr i)).inv₀
      (fun p => hD t ht p i)
  have hf : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)*
        ∏ i, (dispersion (angleTuple r p.1 i) (angleTuple r p.2 i) t)⁻¹) := by
    have hc := hA.mul hP
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

theorem spatialAmplitude_continuous_of_no_poles {N : ℕ} {r : ℝ} (hr : 0 < r)
    (s : ℂ) (hD : ∀ p : (Fin N → ℝ) × (Fin N → ℝ), ∀ i,
      sourceS s-angularDispersionTrace r i p ≠ 0)
    (A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hF : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)*
        sourceResolventProduct (angularDispersionTrace r) s p)) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)) := by
  have hP : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      ∏ i, (sourceS s-angularDispersionTrace r i p)) := by
    apply continuous_finsetProd
    intro i _
    exact continuous_const.sub (angularDispersionTrace_continuous hr i)
  convert! hF.mul hP using 1
  funext p
  have hp0 : (∏ i, (sourceS s-angularDispersionTrace r i p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hD p i)
  change _ = (A (angleTuple r p.1) (angleTuple r p.2)*
    (∏ i, (sourceS s-angularDispersionTrace r i p)⁻¹))*
    ∏ i, (sourceS s-angularDispersionTrace r i p)
  rw [Finset.prod_inv_distrib, mul_assoc, inv_mul_cancel₀ hp0, mul_one]

end
end IsingBulk.First
