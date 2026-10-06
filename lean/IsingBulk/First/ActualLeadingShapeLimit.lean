import IsingBulk.First.ActualShapeNeighborhood
import IsingBulk.First.ShapeCutoffLimit

/-! The actual highest-pole shape asymptotic after the mean residue. Every
amplitude and denominator estimate is discharged for the source expression. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology

/-- A fixed support radius works for every continuous cutoff bounded by one
and equal to one at the stationary point. Its shape profile is fixed before ε
varies. The physical amplitude and nonlinear denominator are literal. -/
theorem actual_leading_shape_sqrt_limit {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (a : OrderedChartData) (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • ∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*chi x*intrinsicLeadingAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^(k+1))
        (𝓝[>] 0) (𝓝 (((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k)*
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
  apply normalized_sqrt_limit_of_scale_limit
  apply postMean_shape_cutoff_limit hn hdegree
    (fun lam x => intrinsicLeadingAmplitude a k (lam^2,x))
    (fun lam x => actualShapeDenominator a (lam^2) x) chi _
    hR (a.Q_pos (Nat.succ_pos n)) a.d_pos hM.le hc hlam₀ hchi hchi0 hchib hchis
  · intro lam hl x hx
    exact ((hdata lam hl x hx).1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  · intro lam hl x hx
    exact ((hdata lam hl x hx).2.2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  · intro lam hl x hx
    exact (hdata lam hl x hx).2.2.2.1
  · intro lam hl x hx
    exact hD (lam^2) x (hlam lam hl).1 ((hlam lam hl).2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_right _ _))
  · exact intrinsicLeadingAmplitude_scale_limit a k he ha hb
  · exact actualShapeDenominator_scale_limit a hb

end
end IsingBulk.First
