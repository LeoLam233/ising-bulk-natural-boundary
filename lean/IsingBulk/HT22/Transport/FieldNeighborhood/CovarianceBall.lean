import IsingBulk.HT22.Transport.FieldNeighborhood.SourceBall

/-! The same quantitative mixed-covariance margin, exposed for collision factors. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

theorem sourceCovariance_margin_on_ball {N : ℕ} (hN : 0<N) (x : SourcePoint N)
    (C H d c η : ℝ) (hC : 0<C) (hH : 0<H) (hd : 0<d) (hc : 0<c)
    (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/(4*C^2))
    (hU : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i,
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (y.1,y.2 i))
    (hD1 : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i j,
      ‖fderiv ℂ (fun z => sourceInverseCoordinate i z-sourceInverseCoordinate j z) y‖≤C*H)
    (hE1 : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i j,
      ‖fderiv ℂ (fun z => sourceInverseVCoordinate i z-sourceInverseVCoordinate j z) y‖≤C)
    (hD0 : ∀ i j, ‖sourceInverseCoordinate i x-sourceInverseCoordinate j x‖≤C*H*d)
    (hE0 : ∀ i j, ‖sourceInverseVCoordinate i x-sourceInverseVCoordinate j x‖≤C*d)
    (hR0 : c*H*d^2≤‖sourceCovariance x.1 x.2‖) :
    ∀ y∈ball x (η*d/(N:ℝ)^2), c*H*d^2/2≤‖sourceCovariance y.1 y.2‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hradius : 0<η*d/(N:ℝ)^2 := by positivity
  have hx : x∈closedBall x (η*d/(N:ℝ)^2) := mem_closedBall_self hradius.le
  intro y hy
  have hyc := ball_subset_closedBall hy
  have hdist : ‖y-x‖≤η*d/(N:ℝ)^2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hyc
  have hdu (i j : Fin N) :
      ‖(sourceInverseCoordinate i y-sourceInverseCoordinate j y)-
        (sourceInverseCoordinate i x-sourceInverseCoordinate j x)‖≤C*H*η*d/(N:ℝ)^2 := by
    have hl := (convex_closedBall x (η*d/(N:ℝ)^2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((sourceInverseCoordinate_analyticAt z i (hU z hz i)).sub
        (sourceInverseCoordinate_analyticAt z j (hU z hz j))).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => hD1 z hz i j) hx hyc
    exact hl.trans (by calc
      _ ≤ (C*H)*(η*d/(N:ℝ)^2) := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = _ := by ring)
  have hdv (i j : Fin N) :
      ‖(sourceInverseVCoordinate i y-sourceInverseVCoordinate j y)-
        (sourceInverseVCoordinate i x-sourceInverseVCoordinate j x)‖≤C*η*d/(N:ℝ)^2 := by
    have hl := (convex_closedBall x (η*d/(N:ℝ)^2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((sourceInverseVCoordinate_analyticAt z i (hU z hz i)).sub
        (sourceInverseVCoordinate_analyticAt z j (hU z hz j))).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => hE1 z hz i j) hx hyc
    exact hl.trans (by calc
      _ ≤ C*(η*d/(N:ℝ)^2) := mul_le_mul_of_nonneg_left hdist hC.le
      _ = _ := by ring)
  have hmargin := mixedCovariance_scaled_margin hN
    (fun i => sourceInverseCoordinate i x) (fun i => sourceInverseVCoordinate i x)
    (fun i => sourceInverseCoordinate i y) (fun i => sourceInverseVCoordinate i y)
    C H d c η hC hH hd hc hη hη1 hηc hD0 hE0 hdu hdv hR0
  exact hmargin

end
end IsingBulk.HT22
