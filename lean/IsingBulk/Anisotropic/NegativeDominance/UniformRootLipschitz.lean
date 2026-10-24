import IsingBulk.Anisotropic.RegularEdges.RootJets
import Mathlib.Analysis.Calculus.MeanValue

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Metric
open scoped Topology

/-- Uniform complex-parameter Lipschitz control of every angular root, proved
from the actual analytic root and Cauchy estimates, not an assumed modulus. -/
theorem edgeParamRoot_uniform_lipschitz_zero {b : ℝ} {B : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0) :
    ∃ δ L : ℝ, 0<δ ∧ 0<L ∧ ∀ u : ℂ, ‖u‖<δ →
      ∀ q∈Icc (-Real.pi) Real.pi,
        AnalyticAt ℂ (fun v => edgeParamRoot b B v q) u ∧
        ‖edgeParamRoot b B u q-edgeParamRoot b B 0 q‖≤L*‖u‖ := by
  obtain ⟨δ,hδ,hj⟩ := edgeParamRoot_uniform_derivatives hb hB hBa
  refine ⟨δ,2/δ,hδ,by positivity,?_⟩
  intro u hu q hq
  have hdiff (v : ℂ) (hv : v∈ball 0 δ) : DifferentiableAt ℂ (fun w => edgeParamRoot b B w q) v :=
    (hj v (by simpa only [mem_ball,dist_zero_right] using hv) q hq).1.differentiableAt
  have hder (v : ℂ) (hv : v∈ball 0 δ) : ‖deriv (fun w => edgeParamRoot b B w q) v‖≤2/δ := by
    have hh := (hj v (by simpa only [mem_ball,dist_zero_right] using hv) q hq).2 1
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
    simpa using hh
  refine ⟨(hj u hu q hq).1,?_⟩
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hder (convex_ball (0 : ℂ) δ)
    (mem_ball_self hδ) (show u∈ball 0 δ by simpa only [mem_ball,dist_zero_right] using hu)
  simpa only [sub_zero] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
