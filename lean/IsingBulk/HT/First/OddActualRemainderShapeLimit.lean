import IsingBulk.First.ActualShapeNeighborhood
import IsingBulk.HT.First.OddRemainderLimit

/-! Actual critical-pole remainder of the odd density. The physical source
neighborhood supplies all hypotheses; ε times its integral tends to zero.
This theorem does not assert a uniform O(1) bound on the unscaled remainder. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First
open scoped Topology

theorem actual_remainder_shape_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (a : OrderedChartData)
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

end
end IsingBulk.HT.First
