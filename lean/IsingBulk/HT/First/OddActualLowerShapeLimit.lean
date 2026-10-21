import IsingBulk.HT.First.OddLowerPoleLimit
import IsingBulk.First.ActualLowerDerivativeBound

/-! All actual lower post-mean jets vanish after multiplication by ε, including
j=k−1. The generated combined numerator is the existing literal source jet;
its bound is proved before varying ε and shape. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First
open scoped Topology

theorem actual_lower_postMean_shape_epsilon_limit {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k-1) (hj : j < k) (a : OrderedChartData)
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

end
end IsingBulk.HT.First
