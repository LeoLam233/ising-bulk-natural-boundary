import IsingBulk.First.RegularIntegratedMean
import IsingBulk.HT.First.OddLowerPoleLimit
import IsingBulk.HT.First.OddLimitTransfer

/-! Actual negative-family FIRST attachment on the original integer-angle
selected point. No reflected positive prime family or analytic certificate
is substituted for the literal physical source. -/
namespace IsingBulk.HT.First.Regular
noncomputable section
open Complex MeasureTheory Filter Set Metric IsingBulk.Branch IsingBulk.First IsingBulk.First.Regular
open scoped Topology BigOperators ContDiff

def intrinsicCombinedAmplitude {n : ℕ} (a : RegularChartData) (j : ℕ)
    (p : ℝ × ShapeSpace n) : ℂ :=
  intrinsicLeadingAmplitude a j p + actualShapeDenominator a p.1 p.2 * intrinsicRemainderAmplitude a j p

theorem intrinsicCombinedAmplitude_uniform_neighborhood {n : ℕ} (a : RegularChartData) (j : ℕ) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ epsilon : ℝ, ∀ x : ShapeSpace n,
      |epsilon| < r → ‖x‖ < r →
      ContinuousAt (intrinsicCombinedAmplitude a j) (epsilon,x) ∧
      ContinuousAt (fun q : ℝ × ShapeSpace n => actualShapeDenominator a q.1 q.2) (epsilon,x) ∧
      ‖intrinsicCombinedAmplitude a j (epsilon,x)‖ ≤ M := by
  have hcont : ∀ᶠ p : ℝ × ShapeSpace n in 𝓝 (0,0),
      ContinuousAt (intrinsicCombinedAmplitude a j) p ∧
      ContinuousAt (fun q : ℝ × ShapeSpace n => actualShapeDenominator a q.1 q.2) p := by
    filter_upwards [intrinsic_actual_eventual_continuity (n := n) a j] with p hp
    exact ⟨hp.1.add (hp.2.2.mul hp.2.1),hp.2.2⟩
  let M := ‖intrinsicCombinedAmplitude a j (0,(0:ShapeSpace n))‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : ∀ᶠ p : ℝ × ShapeSpace n in 𝓝 (0,0), ‖intrinsicCombinedAmplitude a j p‖ ≤ M :=
    ((hcont.self_of_nhds.1.norm).eventually (Iio_mem_nhds (by dsimp [M]; linarith))).mono
      (fun _ h => h.le)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hcont.and hb)
  refine ⟨r,M,hr,hM,?_⟩
  intro epsilon x he hx
  have hm : (epsilon,x) ∈ ball (0,(0:ShapeSpace n)) r := by
    rw [mem_ball,dist_eq_norm]
    change max ‖epsilon-0‖ ‖x-0‖ < r
    simpa only [sub_zero,Real.norm_eq_abs,max_lt_iff] using And.intro he hx
  exact ⟨(hball hm).1.1,(hball hm).1.2,(hball hm).2⟩

theorem actual_lower_postMean_shape_epsilon_limit {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k-1) (hj : j < k) (a : RegularChartData)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon • ∫ x : ShapeSpace n,
        chi x*intrinsicPostMeanDerivative a j epsilon x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsicCombinedAmplitude_uniform_neighborhood (n := n) a j
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  obtain ⟨rE,hrE,hE⟩ := intrinsic_postMean_derivative_expansion (n := n) a j hb
  let R := min rA (min rD rE)
  have hR : 0 < R := lt_min hrA (lt_min hrD hrE)
  have hRA : R ≤ rA := min_le_left _ _
  have hRD : R ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hRE : R ≤ rE := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R,hR,?_⟩
  intro chi hchi hchib hchis
  have hdata (epsilon : ℝ) (he : epsilon ∈ Ioo 0 R)
      (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA epsilon x (by rw [abs_of_pos he.1]; exact he.2.trans_le hRA)
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le hRA)
  have ht := subcritical_pole_setIntegral_epsilon_limit hn (show 1 ≤ j+1 by omega)
    (by omega : 2*((j+1)-1) ≤ n-1+(n+1)*n)
    (fun epsilon x => chi x*intrinsicCombinedAmplitude a j (epsilon,x))
    (fun epsilon x => actualShapeDenominator a epsilon x) (R := R) hM.le hc hR
    (fun epsilon he => hchi.continuousOn.mul (fun x hx =>
      ((hdata epsilon he x hx).1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt))
    (fun epsilon he x hx => ((hdata epsilon he x hx).2.1.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun epsilon he x hx => by
      rw [norm_mul]
      exact (mul_le_mul (hchib x) (hdata epsilon he x hx).2.2
        (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul M))
    (fun epsilon he x hx => hD epsilon x he.1 (he.2.trans_le hRD)
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le hRD))
  have hs := ht.const_mul (2*(Real.pi:ℂ))
  simp only [mul_zero] at hs
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with epsilon he heR
  have hgap (x : ShapeSpace n) (hx : ‖x‖ < R) :=
    hD epsilon x he (heR.trans_le hRD) (hx.trans_le hRD)
  have heq : (fun x : ShapeSpace n => chi x*intrinsicPostMeanDerivative a j epsilon x) =
      fun x => (2*(Real.pi:ℂ))*((shapeVandermondeSq x:ℂ)*chi x*
        intrinsicCombinedAmplitude a j (epsilon,x)/(actualShapeDenominator a epsilon x)^(j+1)) := by
    funext x
    by_cases hx : chi x = 0
    · simp only [hx,zero_mul,mul_zero,zero_div]
    · have hxr := hchis x hx
      have hdne : actualShapeDenominator a epsilon x ≠ 0 := by
        intro hz
        have hg := hgap x hxr
        rw [hz,norm_zero] at hg
        have hp : 0 < c*(epsilon+‖x‖^2) := mul_pos hc (add_pos_of_pos_of_nonneg he (sq_nonneg _))
        linarith
      rw [hE epsilon x he (heR.trans_le hRE) (hxr.trans_le hRE)]
      unfold intrinsicCombinedAmplitude
      rw [pow_succ]
      field_simp [hdne]
  rw [heq,integral_const_mul,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have hi : (∫ x : ShapeSpace n, (shapeVandermondeSq x:ℂ)*chi x*
          intrinsicCombinedAmplitude a j (epsilon,x)/(actualShapeDenominator a epsilon x)^(j+1)) =
        ∫ x : ShapeSpace n, (shapeVandermondeSq x:ℂ)*(chi x*
          intrinsicCombinedAmplitude a j (epsilon,x))/(actualShapeDenominator a epsilon x)^(j+1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    rw [hi]
    simp only [Complex.real_smul]
    ring
  · intro x hx
    have hz : chi x = 0 := by
      by_contra hh
      exact hx (mem_ball_zero_iff.mpr (hchis x hh))
    simp only [hz,zero_mul,mul_zero,zero_div]

theorem actual_localized_postMean_lower_epsilon_limit {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k-1) (hj : j < k) (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon •
        (deriv^[j] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Rl,hRl,hL⟩ := actual_lower_postMean_shape_epsilon_limit hn hdegree hj a hb
  obtain ⟨Ri,hRi,hI⟩ := actual_postMean_integral_interchange (n := n) a ha hb
  refine ⟨min Rl Ri,lt_min hRl hRi,?_⟩
  intro chi hchi hchib hchis
  have ht := (hL chi hchi hchib (fun x hx => (hchis x hx).trans_le (min_le_left _ _))).const_smul
    (Real.sqrt (n+1))⁻¹
  simp only [smul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hRi).filter_mono nhdsWithin_le_nhds] with epsilon he heRi
  rw [hI epsilon he heRi chi hchi (fun x hx => (hchis x hx).trans_le (min_le_right _ _))]
  have hi := integral_shapeExtend n (fun x => chi x*intrinsicPostMeanDerivative a j epsilon x)
  have hid : localizedPostMeanDerivativeIntegral a j chi epsilon =
      (Real.sqrt (n+1))⁻¹ • ∫ x : ShapeSpace n, chi x*intrinsicPostMeanDerivative a j epsilon x := by
    simpa only [IsingBulk.First.Regular.localizedPostMeanDerivativeIntegral,
      IsingBulk.First.Regular.intrinsicPostMeanDerivative,
      intrinsicShapeCoordinates_shapeCoordinateEquiv] using hi
  rw [hid,smul_comm]

theorem actual_local_mean_lower_epsilon_limit {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k-1) (hj : j < k) (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R : ℝ, 0 < R ∧ ∀ eta : ℝ → ℂ, Continuous eta →
        (∀ v : ℝ, |v| ≤ delta → eta v=1) →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, ‖chi x‖ ≤ 1) →
          (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          Tendsto (fun epsilon : ℝ => epsilon •
            (deriv^[j] (localizedSmoothMeanIntegral a chi eta
              (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon))
            (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Rp,hRp,hP⟩ := actual_localized_postMean_lower_epsilon_limit hn hdegree hj a ha hb
  obtain ⟨Dd,hDd,hD⟩ := actual_integrated_mean_derivative_decomposition (n := n) a ha hb
  obtain ⟨De,hDe,hE⟩ := actual_mean_error_shape_sqrt_limit (n := n) a ha hb
  refine ⟨min Dd De,lt_min hDd hDe,?_⟩
  intro delta hd hdD
  obtain ⟨Rd,epsilon₀,hRd,he0,hDec⟩ := hD delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨Re,hRe,hErr⟩ := hE delta hd (hdD.trans (min_le_right _ _))
  let R := min Rp (min Rd Re)
  have hR : 0 < R := lt_min hRp (lt_min hRd hRe)
  have hRRp : R ≤ Rp := min_le_left _ _
  have hRRd : R ≤ Rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRRe : R ≤ Re := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R,hR,?_⟩
  intro eta heta heta1 chi hchi hchib hchis
  have hPost := hP chi hchi hchib (fun x hx => (hchis x hx).trans_le hRRp)
  have hError := epsilon_limit_of_sqrt_limit_zero
    (hErr eta heta chi hchi hchib (fun x hx => (hchis x hx).trans_le hRRe) j)
  have ht := hPost.add hError
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds he0).filter_mono nhdsWithin_le_nhds] with epsilon he he0'
  rw [hDec eta heta heta1 chi hchi (fun x hx => (hchis x hx).trans_le hRRd) epsilon he he0',smul_add]

end
end IsingBulk.HT.First.Regular
