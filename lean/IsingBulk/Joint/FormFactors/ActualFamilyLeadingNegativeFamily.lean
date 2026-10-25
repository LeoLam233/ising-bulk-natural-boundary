import IsingBulk.Joint.FormFactors.ComplexRatioBounds
import IsingBulk.Joint.RegularEdges.NegativeEvenIdentity

/-! The actual negative-even low-temperature ratio family uses the additive
upper coordinate C+B-b. This is a separate constructed implicit family from
the scaled negative-odd coordinate (C+B-b)/B. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Joint analyticity of the additive negative-edge coordinate. -/
theorem negative_additive_edge_analyticAt (b : ℂ) {K : Coupling} (hS : S K≠0) :
    AnalyticAt ℂ (Transverse.negativeParameter b) K :=
  ((transferC_analyticAt hS).add (transferB_analyticAt hS)).sub analyticAt_const

/-- The genuine complex-ratio implicit family at a negative even LT edge.
The physical prefactor is fixed, and the anisotropy has a common negative
imaginary-part margin on the constructed doubled polydisk. -/
theorem negative_even_low_complex_ratio_family {b z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (he0 : Transverse.negativeParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z=>Transverse.negativeParameter b (z,lam₀*z)) z₀≠0) :
    Nonempty (ComplexRatioFamily (Transverse.negativeParameter b) lowPrefactor (-1) z₀ lam₀) :=
  exists_admissible_complex_ratio_family (negative_additive_edge_analyticAt b hS) he0 hd hS
    (by simpa using hB) (RegularEdges.lowPrefactor_boundary_analyticAt hK hp)
    (lowPrefactor_ne_zero _)

namespace ComplexRatioFamily
variable {b : ℝ} {amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily (Transverse.negativeParameter (b:ℂ)) amp (-1) z₀ lam₀)

theorem negative_additive_ratio_normalization_germ {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) :
    ∀ᶠu : ℂ in 𝓝 0,Transverse.negativeParameter b (F.coupling (u,lam))=u := by
  filter_upwards [ball_mem_nhds (0:ℂ) F.radius_pos] with u hu
  have hq : (u,lam)∈F.polydisk := ⟨ball_subset_closedBall hu,hl⟩
  exact F.edge_eq u lam (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2

theorem negative_additive_ratio_center_analytic {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) : AnalyticAt ℂ F.coupling (0,lam) :=
  F.coupling_analytic 0 lam (F.polydisk_bounds (F.zero_mem_polydisk hl)).1
    (F.polydisk_bounds (F.zero_mem_polydisk hl)).2

theorem negative_additive_ratio_center_scale_ne_zero {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) : S (F.coupling (0,lam))≠0 :=
  F.scale_ne_zero (F.zero_mem_polydisk hl)

theorem negative_additive_ratio_center_anisotropy_neg {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) : (transferB (F.coupling (0,lam))).im<0 := by
  simpa only [neg_one_mul,neg_pos,anisotropy] using F.anisotropy_sign (F.zero_mem_polydisk hl)

end ComplexRatioFamily
end
end IsingBulk.Joint.FormFactors
