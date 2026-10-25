import IsingBulk.Joint.Transverse.FamilyNormalization

namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace FamilyNormalization
variable {f : ℂ × E→ℂ} {eta₀ eta : E} (N : FamilyNormalization f eta₀)

/-- The inverse remains nonramified at every selected family center. -/
theorem inverse_deriv_mul (heta : ‖eta-eta₀‖<N.radius) (hz : f (0,eta)=0)
    (hf : AnalyticAt ℂ f (0,eta)) :
    deriv (fun z=>f (z,eta)) 0 * deriv (fun u=>N.inverse (u,eta)) 0=1 := by
  have ha : AnalyticAt ℂ (fun z=>f (z,eta)) 0 :=
    hf.comp (f:=fun z : ℂ=>(z,eta)) (analyticAt_id.prod analyticAt_const)
  have hb : AnalyticAt ℂ (fun u=>N.inverse (u,eta)) 0 :=
    (N.analytic 0 eta (by simpa using N.radius_pos) heta).comp
      (f:=fun u : ℂ=>(u,eta)) (analyticAt_id.prod analyticAt_const)
  have heq : (fun u=>f (N.inverse (u,eta),eta)) =ᶠ[𝓝 (0:ℂ)] id := N.right_inv_germ heta
  have he : deriv (fun u=>f (N.inverse (u,eta),eta)) 0=1 := by
    simpa using heq.deriv_eq
  have ha' : HasDerivAt (fun z=>f (z,eta)) (deriv (fun z=>f (z,eta)) 0) (N.inverse (0,eta)) := by
    simpa only [N.center eta heta hz] using ha.differentiableAt.hasDerivAt
  have hchain := (ha'.comp 0 hb.differentiableAt.hasDerivAt).deriv
  exact hchain.symm.trans he

theorem inverse_deriv_ne_zero (heta : ‖eta-eta₀‖<N.radius) (hz : f (0,eta)=0)
    (hf : AnalyticAt ℂ f (0,eta)) : deriv (fun u=>N.inverse (u,eta)) 0≠0 := by
  intro h
  have hh := N.inverse_deriv_mul heta hz hf
  rw [h,mul_zero] at hh
  exact zero_ne_one hh

end FamilyNormalization
end
end IsingBulk.Joint.Transverse
