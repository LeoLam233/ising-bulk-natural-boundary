import IsingBulk.HT22.First.LocalLimit.Remainder
import IsingBulk.HT22.First.LocalLimit.LocalIntegral

namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First IsingBulk.HT.First
open scoped Topology
set_option maxHeartbeats 1000000

theorem equalAngle_full_shape_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    let a := equalAngleRegularData α hα hαπ hc
    let k := derivativeOrder (n+1);
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon • ∫ x : ShapeSpace n,
        chi x*Regular.intrinsicPostMeanDerivative a k epsilon x)
        (𝓝[>] 0) (𝓝 (2*(Real.pi:ℂ)*
          (Regular.intrinsicLeadingAmplitude a k (0,(0:ShapeSpace n)))*
            shapePeriodIntrinsic n k (2*(n+1)) (-I*(Real.cos α/Real.sin α)))) := by
  dsimp only
  let a := equalAngleRegularData α hα hαπ hc
  let k := derivativeOrder (n+1)
  obtain ⟨Rl,hRl,hL⟩ := equalAngle_leading_shape_limit hn ho α hα hαπ hc ha
  obtain ⟨Rr,hRr,hR⟩ := equalAngle_remainder_shape_limit hn ho α hα hαπ hc ha
  obtain ⟨Ri,hRi,hI⟩ := equalAngle_pole_integrable hn α hα hαπ hc ha k
  obtain ⟨Re,hRe,hE⟩ := Regular.intrinsic_postMean_derivative_expansion (n := n) a k ha
  let R := min Rl (min Rr (min Ri Re))
  have hpos : 0 < R := lt_min hRl (lt_min hRr (lt_min hRi hRe))
  have hl : R ≤ Rl := min_le_left _ _
  have hr : R ≤ Rr := (min_le_right _ _).trans (min_le_left _ _)
  have hi : R ≤ Ri := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heq : R ≤ Re := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨R,hpos,?_⟩
  intro chi hchi hchi0 hchib hchis
  have hLs := hL chi hchi hchi0 hchib (fun x hx => (hchis x hx).trans_le hl)
  have hRs := hR chi hchi hchib (fun x hx => (hchis x hx).trans_le hr)
  have ht := (hLs.add hRs).const_mul (2*(Real.pi:ℂ))
  simp only [add_zero, ← mul_assoc] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds] with epsilon he heR
  obtain ⟨hIL,hIR⟩ := hI chi hchi hchib (fun x hx => (hchis x hx).trans_le hi) epsilon ⟨he,heR.trans_le hi⟩
  have hInt : (∫ x : ShapeSpace n, chi x*Regular.intrinsicPostMeanDerivative a k epsilon x) =
      2*(Real.pi:ℂ)*((∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*chi x*Regular.intrinsicLeadingAmplitude a k (epsilon,x)/
          (Regular.actualShapeDenominator a epsilon x)^(k+1))+
        ∫ x : ShapeSpace n,
          (shapeVandermondeSq x:ℂ)*chi x*Regular.intrinsicRemainderAmplitude a k (epsilon,x)/
            (Regular.actualShapeDenominator a epsilon x)^k) := by
    rw [← integral_add hIL hIR, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : chi x = 0
      · simp only [hx, zero_mul, mul_zero, zero_div, zero_add]
      · rw [hE epsilon x he (heR.trans_le heq) ((hchis x hx).trans_le heq)]
        ring
  rw [hInt]
  simp only [Complex.real_smul]
  ring

/-- The original dependent-angle coordinates retain the exact inverse square
root Gram determinant. -/
theorem equalAngle_coordinate_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    let a := equalAngleRegularData α hα hαπ hc
    let k := derivativeOrder (n+1)
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      Continuous χ → χ 0=1 → (∀ x,‖χ x‖≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε • Regular.localizedPostMeanDerivativeIntegral a k χ ε)
        (𝓝[>] 0) (𝓝 (
          -I*(equalAngleAmplitude (n+1) α:ℂ)*(k.factorial:ℂ)*(2*(n+1:ℂ))^k*
            exp (-(α:ℂ)*I)^k * shapePeriod n k (2*(n+1)) (-I*(Real.cos α/Real.sin α)))) := by
  dsimp only
  let a := equalAngleRegularData α hα hαπ hc
  let k := derivativeOrder (n+1)
  obtain ⟨R,hR,h⟩ := equalAngle_full_shape_limit hn ho α hα hαπ hc ha
  refine ⟨R,hR,?_⟩
  intro χ hχ hχ0 hχb hχs
  have ht := (h χ hχ hχ0 hχb hχs).const_smul (Real.sqrt (n+1))⁻¹
  convert ht using 1
  · funext ε
    have hi := integral_shapeExtend n (fun x => χ x*Regular.intrinsicPostMeanDerivative a k ε x)
    have hid : Regular.localizedPostMeanDerivativeIntegral a k χ ε =
        (Real.sqrt (n+1))⁻¹ • ∫ x : ShapeSpace n, χ x*Regular.intrinsicPostMeanDerivative a k ε x := by
      simpa only [Regular.localizedPostMeanDerivativeIntegral, Regular.intrinsicPostMeanDerivative,
        intrinsicShapeCoordinates_shapeCoordinateEquiv] using hi
    rw [hid,smul_comm]
  · congr 1
    rw [shapePeriod_eq_intrinsic]
    have hc0 := equalAngle_highest_pole_center ho α hα hαπ hc ha
    simp only [Complex.real_smul] at *
    rw [← hc0]
    ring

end
end IsingBulk.HT22.LocalLimit
