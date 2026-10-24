import IsingBulk.Anisotropic.RegularEdges.LeadingQuotient

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_parameter_deriv {F : ℂ×E→ℂ} {p : ℂ×E} (hF : AnalyticAt ℂ F p) :
    AnalyticAt ℂ (fun q : ℂ×E => deriv (fun u => F (u,q.2)) q.1) p := by
  have ha : AnalyticAt ℂ (fun q : ℂ×E => fderiv ℂ F q (1,0)) p :=
    by simpa using! ((ContinuousLinearMap.apply ℂ ℂ ((1,0):ℂ×E)).analyticAt _).comp hF.fderiv
  apply ha.congr
  filter_upwards [hF.eventually_analyticAt] with q hq
  have hg : HasDerivAt (fun u : ℂ => (u,q.2)) (1,0) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact (hq.differentiableAt.hasFDerivAt.comp_hasDerivAt q.1 hg).deriv.symm

theorem quotientJetNumerator_joint_analyticAt {A D : ℂ×E→ℂ} {p : ℂ×E}
    (hA : AnalyticAt ℂ A p) (hD : AnalyticAt ℂ D p) (n : ℕ) :
    AnalyticAt ℂ (fun q : ℂ×E => quotientJetNumerator
      (fun u => A (u,q.2)) (fun u => D (u,q.2)) n q.1) p := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    exact (hD.mul (analyticAt_parameter_deriv ih)).sub
      ((analyticAt_const.mul (analyticAt_parameter_deriv hD)).mul ih)

end
end IsingBulk.Anisotropic.RegularEdges
