import IsingBulk.HT.First.OddActualLeadingShapeLimit
import IsingBulk.HT.First.OddActualRemainderShapeLimit
import IsingBulk.HT.First.OddActualShapeIntegrability
import IsingBulk.First.ActualShapeDerivative

/-! Full literal odd post-mean density at the HT derivative order: ε times the
integral has its nonzero local coefficient. Both pole terms are integrable
before splitting. The global contour complement is a separate obligation. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First
open scoped Topology

theorem actual_postMean_shape_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (a : OrderedChartData) (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon • ∫ x : ShapeSpace n,
        chi x*intrinsicPostMeanDerivative a k epsilon x)
        (𝓝[>] 0) (𝓝 (2*(Real.pi:ℂ)*
          ((-I*((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k))*
            shapePeriodIntrinsic n k (a.Q (n+1)) (-I*a.d)))) := by
  obtain ⟨Rl,hRl,hL⟩ := actual_leading_shape_epsilon_limit hn hk hdegree a ho ha hb
  obtain ⟨Rr,hRr,hR⟩ := actual_remainder_shape_epsilon_limit hn hk hdegree a hb
  obtain ⟨Ri,hRi,hI⟩ := actual_pole_shapes_integrable hn a k hb
  obtain ⟨Re,hRe,hE⟩ := intrinsic_postMean_derivative_expansion (n := n) a k hb
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
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds] with epsilon he heR
  obtain ⟨hIL,hIR⟩ := hI chi hchi hchib (fun x hx => (hchis x hx).trans_le hi) epsilon ⟨he,heR.trans_le hi⟩
  have hInt : (∫ x : ShapeSpace n, chi x*intrinsicPostMeanDerivative a k epsilon x) =
      2*(Real.pi:ℂ)*((∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*chi x*intrinsicLeadingAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^(k+1))+
        ∫ x : ShapeSpace n,
          (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
            (actualShapeDenominator a epsilon x)^k) := by
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

end
end IsingBulk.HT.First
