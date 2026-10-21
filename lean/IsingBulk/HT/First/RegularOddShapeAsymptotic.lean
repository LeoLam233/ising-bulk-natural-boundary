import IsingBulk.First.RegularShapeSource
import IsingBulk.HT.First.RegularOddDensityCenter
import IsingBulk.HT.First.OddActualShapeIntegrability
import IsingBulk.HT.First.OddShapeCutoffLimit
import IsingBulk.HT.First.OddLimitTransfer

/-! Actual regular-chart shape scaling and generated physical amplitudes.
All source denominators, shape measures and parameter derivatives are literal. -/
namespace IsingBulk.HT.First.Regular
noncomputable section
open Complex MeasureTheory Filter Set Metric IsingBulk.Branch IsingBulk.First IsingBulk.First.Regular
open scoped Topology BigOperators

theorem intrinsicLeadingAmplitude_odd_scale_limit {n : ℕ} (a : RegularChartData) (k : ℕ)
    (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) (x : ShapeSpace n) :
    Tendsto (fun lam : ℝ => intrinsicLeadingAmplitude a k (lam^2,lam • x))
      (𝓝[>] 0) (𝓝 (-I*((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k))) := by
  have hp : Tendsto (fun lam : ℝ => (lam^2,lam • x)) (𝓝[>] 0) (𝓝 (0,0)) := by
    have hc : Continuous (fun lam : ℝ => (lam^2,lam • x)) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have h := (intrinsicLeadingAmplitude_continuousAt_zero a k).tendsto.comp hp
  simpa only [Function.comp_def,IsingBulk.First.Regular.intrinsicLeadingAmplitude,
    IsingBulk.First.Regular.intrinsicRadialEmbedding_zero,
    actualLeadingAmplitude_odd_center a n k ho ha hb] using h

theorem actual_pole_shapes_integrable {n : ℕ} (hn : 1 ≤ n)
    (a : RegularChartData) (k : ℕ)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ,0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x,‖chi x‖ ≤ 1) → (∀ x,chi x ≠ 0 → ‖x‖ < R) →
      ∀ epsilon ∈ Ioo 0 R,
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*intrinsicLeadingAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^(k+1)) ∧
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^k) := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsic_actual_uniform_neighborhood (n := n) a k
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  let R := min rA rD
  refine ⟨R,lt_min hrA hrD,?_⟩
  intro chi hchi hchib hchis epsilon he
  have hdata (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA epsilon x (by rw [abs_of_pos he.1]; exact he.2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_left _ _))
  have hDc : ContinuousOn (actualShapeDenominator a epsilon) (ball 0 R) := fun x hx =>
    ((hdata x hx).2.2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hDb (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hD epsilon x he.1 (he.2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_right _ _))
  constructor
  · exact shape_cutoff_pole_integrable_positive_gap hn (k+1) _ _ chi R he.1 hM.le hc hchi hchib hchis
      (fun x hx => ((hdata x hx).1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
      hDc (fun x hx => (hdata x hx).2.2.2.1) hDb
  · exact shape_cutoff_pole_integrable_positive_gap hn k _ _ chi R he.1 hM.le hc hchi hchib hchis
      (fun x hx => ((hdata x hx).2.1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
      hDc (fun x hx => (hdata x hx).2.2.2.2) hDb

theorem actual_leading_shape_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (a : RegularChartData) (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon • ∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*chi x*intrinsicLeadingAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^(k+1))
        (𝓝[>] 0) (𝓝 ((-I*((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k))*
          shapePeriodIntrinsic n k (a.Q (n+1)) (-I*a.d))) := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsic_actual_uniform_neighborhood (n := n) a k
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  let R := min rA rD
  have hR : 0 < R := lt_min hrA hrD
  refine ⟨R,hR,?_⟩
  intro chi hchi hchi0 hchib hchis
  let lam₀ := min 1 R
  have hlam₀ : 0 < lam₀ := lt_min zero_lt_one hR
  have hlam (lam : ℝ) (hl : lam ∈ Ioo 0 lam₀) : 0 < lam^2 ∧ lam^2 < R := by
    have hl1 : lam < 1 := hl.2.trans_le (min_le_left _ _)
    have hlR : lam < R := hl.2.trans_le (min_le_right _ _)
    exact ⟨sq_pos_of_pos hl.1, by nlinarith [hl.1]⟩
  have hdata (lam : ℝ) (hl : lam ∈ Ioo 0 lam₀) (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA (lam^2) x (by rw [abs_of_nonneg (sq_nonneg _)]; exact (hlam lam hl).2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_left _ _))
  apply normalized_epsilon_limit_of_scale_limit
  apply postMean_odd_shape_cutoff_limit hn hk hdegree
    (fun lam x => intrinsicLeadingAmplitude a k (lam^2,x))
    (fun lam x => actualShapeDenominator a (lam^2) x) chi _
    hR (a.Q_pos (Nat.succ_pos n)) a.d_ne_zero hM.le hc hlam₀ hchi hchi0 hchib hchis
  · intro lam hl x hx
    exact ((hdata lam hl x hx).1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  · intro lam hl x hx
    exact ((hdata lam hl x hx).2.2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  · intro lam hl x hx
    exact (hdata lam hl x hx).2.2.2.1
  · intro lam hl x hx
    exact hD (lam^2) x (hlam lam hl).1 ((hlam lam hl).2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_right _ _))
  · exact intrinsicLeadingAmplitude_odd_scale_limit a k ho ha hb
  · exact actualShapeDenominator_scale_limit a hb

theorem actual_remainder_shape_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (a : RegularChartData)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ,0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x,‖chi x‖ ≤ 1) → (∀ x,chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon • ∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^k) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsic_actual_uniform_neighborhood (n := n) a k
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  let R := min rA rD
  have hR : 0 < R := lt_min hrA hrD
  refine ⟨R,hR,?_⟩
  intro chi hchi hchib hchis
  have hdata (epsilon : ℝ) (he : epsilon ∈ Ioo 0 R)
      (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA epsilon x (by rw [abs_of_pos he.1]; exact he.2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_left _ _))
  have ht := odd_remainder_setIntegral_epsilon_limit hn hk hdegree
    (fun epsilon x => chi x*intrinsicRemainderAmplitude a k (epsilon,x))
    (fun epsilon x => actualShapeDenominator a epsilon x) (R := R) hM.le hc hR
    (fun epsilon he => hchi.continuousOn.mul (fun x hx =>
      ((hdata epsilon he x hx).2.1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt))
    (fun epsilon he x hx => ((hdata epsilon he x hx).2.2.1.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun epsilon he x hx => by
      rw [norm_mul]
      exact (mul_le_mul (hchib x) (hdata epsilon he x hx).2.2.2.2
        (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul M))
    (fun epsilon he x hx => hD epsilon x he.1 (he.2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_right _ _)))
  apply ht.congr'
  exact Eventually.of_forall fun epsilon => by
    dsimp only
    congr 1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    · intro x hx
      have hz : chi x = 0 := by
        by_contra hh
        exact hx (mem_ball_zero_iff.mpr (hchis x hh))
      simp only [hz,zero_mul,mul_zero,zero_div]

theorem actual_postMean_shape_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (a : RegularChartData) (ho : Odd (n+1))
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
end IsingBulk.HT.First.Regular
