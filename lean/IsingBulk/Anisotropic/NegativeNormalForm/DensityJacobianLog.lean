import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianSchwarz
import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianSymmetry
import IsingBulk.Anisotropic.Final.ContinuousBranch
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology

theorem exists_normalized_analytic_log_ball {f : ℂ→ℂ} {R : ℝ} (hR : 0<R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hf0 : f 0=1)
    (hn : ∀z∈ball 0 R,f z≠0) :
    ∃L : ℂ→ℂ,AnalyticOnNhd ℂ L (ball 0 R) ∧ L 0=0 ∧ ∀z∈ball 0 R,Complex.exp (L z)=f z := by
  have h0 : (0:ℂ)∈ball 0 R := mem_ball_self hR
  have hsc : IsSimplyConnected (ball (0:ℂ) R) := by
    let : ContractibleSpace (ball (0:ℂ) R) := (convex_ball (0:ℂ) R).contractibleSpace ⟨0,h0⟩
    change SimplyConnectedSpace _
    infer_instance
  obtain ⟨g,hgc,hge⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_ball hf.continuousOn
    (by rintro ⟨z,hz,he⟩; exact hn z hz he)
  have hga : AnalyticOnNhd ℂ g (ball 0 R) := by
    intro z hz
    apply analyticAt_of_analytic_composition (hgc.continuousAt (isOpen_ball.mem_nhds hz))
      analyticAt_id.cexp (by change deriv Complex.exp (g z)≠0; rw [(Complex.hasDerivAt_exp (g z)).deriv]; exact Complex.exp_ne_zero _)
    apply (hf z hz).congr
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (hge hw).symm
  dsimp only [Function.comp_def] at hge
  refine ⟨fun z => g z-g 0,fun z hz => (hga z hz).sub analyticAt_const,sub_self _,?_⟩
  intro z hz
  have hz' : Complex.exp (g z)=f z := hge hz
  have h0' : Complex.exp (g 0)=f 0 := hge h0
  rw [Complex.exp_sub,hz',h0',hf0,div_one]

theorem analytic_log_quadratic_bound {f : ℂ→ℂ} {R M : ℝ} (hR : 0<R) (hM : 0<M)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hf0 : f 0=1) (hd0 : deriv f 0=0)
    (hn : ∀z∈ball 0 R,f z≠0) (hb : ∀z∈ball 0 R,‖f z‖≤Real.exp M) :
    ∃L : ℂ→ℂ,AnalyticOnNhd ℂ L (ball 0 R) ∧ L 0=0 ∧
      (∀z∈ball 0 R,Complex.exp (L z)=f z) ∧
      ∀z : ℂ,‖z‖≤R/2 → ‖L z‖≤4*M*(‖z‖/R)^2 := by
  obtain ⟨L,hLa,hL0,he⟩ := exists_normalized_analytic_log_ball hR hf hf0 hn
  have h0 : (0:ℂ)∈ball 0 R := mem_ball_self hR
  have hevent : (fun z => Complex.exp (L z))=ᶠ[𝓝 (0:ℂ)] f := by
    filter_upwards [ball_mem_nhds (0:ℂ) hR] with z hz using he z hz
  have hder := hevent.deriv_eq
  rw [((hLa 0 h0).differentiableAt.hasDerivAt.cexp).deriv,hd0,hL0,Complex.exp_zero,one_mul] at hder
  have hRe : ∀z∈ball 0 R,(L z).re≤M := by
    intro z hz
    have hh := hb z hz
    rw [←he z hz,Complex.norm_exp] at hh
    exact Real.exp_le_exp.mp hh
  exact ⟨L,hLa,hL0,he,fun z hz => analytic_re_bound_quadratic hR hM hLa hL0 hder hRe hz⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
