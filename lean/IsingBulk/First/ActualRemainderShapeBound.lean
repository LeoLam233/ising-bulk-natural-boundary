import IsingBulk.First.ActualShapeNeighborhood
import IsingBulk.First.ShapeCutoffBounds

/-! The actual generated lower-pole remainder has a parameter-independent
integrable majorant on the fixed support ball. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology

theorem actual_remainder_shape_uniform_bound {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k) (a : OrderedChartData)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R B : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ epsilon ∈ Ioo 0 R,
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^k) ∧
        ‖∫ x : ShapeSpace n, (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^k‖ ≤ B := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsic_actual_uniform_neighborhood (n := n) a k
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  let R := min rA rD
  refine ⟨R,(M/c^k)*∫ x : ShapeSpace n in ball 0 R,
    shapeVandermondeSq x/‖x‖^(2*k),lt_min hrA hrD,?_⟩
  intro chi hchi hchib hchis epsilon he
  have hdata (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA epsilon x (by rw [abs_of_pos he.1]; exact he.2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_left _ _))
  have h := shape_cutoff_lower_bound (j := k-1) hn hdegree (by omega)
    (fun x => intrinsicRemainderAmplitude a k (epsilon,x))
    (actualShapeDenominator a epsilon) chi R hM.le hc hchi hchib hchis
    (fun x hx => ((hdata x hx).2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun x hx => ((hdata x hx).2.2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun x hx => (hdata x hx).2.2.2.2) ?_
  · simpa only [Nat.sub_add_cancel hk] using h
  · intro x hx
    have hd := hD epsilon x he.1 (he.2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_right _ _))
    nlinarith [he.1]


theorem actual_remainder_shape_sqrt_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k) (a : OrderedChartData)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • ∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^k) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R,B,hR,h⟩ := actual_remainder_shape_uniform_bound hn hk hdegree a hb
  refine ⟨R,hR,?_⟩
  intro chi hchi hchib hchis
  have hε : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hbnd : IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ))
      (norm ∘ fun epsilon : ℝ => ∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^k) := by
    refine ⟨B,?_⟩
    apply eventually_map.mpr
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with epsilon he heR
    exact (h chi hchi hchib hchis epsilon ⟨he,heR⟩).2
  simpa only [Pi.smul_apply] using!
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hε hbnd

end
end IsingBulk.First
