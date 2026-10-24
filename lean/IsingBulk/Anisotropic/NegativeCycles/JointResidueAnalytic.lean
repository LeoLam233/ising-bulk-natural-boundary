import IsingBulk.Anisotropic.NegativeCycles.JointDensityAnalytic
import IsingBulk.Anisotropic.NegativeCycles.ActualResidueSlope

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter
open scoped Topology
set_option maxHeartbeats 800000

theorem poleParameterDerivative_joint_analyticAt {n : ℕ} (B : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (hF : AnalyticAt ℂ (fun z : Config n × ℂ => poleEquation B phi hphi d z.2 z.1) (v,t)) :
    AnalyticAt ℂ (fun z : Config n × ℂ => poleParameterDerivative B phi hphi d z.2 z.1) (v,t) := by
  let F : Config n × ℂ→ℂ := fun z => poleEquation B phi hphi d z.2 z.1
  let L : ((Config n × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,1)
  have hg : AnalyticAt ℂ (fun z => L (fderiv ℂ F z)) (v,t) := (L.analyticAt _).comp hF.fderiv
  apply hg.congr
  filter_upwards [hF.eventually_analyticAt] with z hz
  exact (poleParameterDerivative_eq_fderiv B phi hphi d z.2 z.1 hz.differentiableAt).symm

/-- Genuine residue holomorphy on a scalar-controlled common neighborhood. -/
theorem poleResidue_local_uniform_analytic (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hr : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) :
    ∃r : ℝ,0<r ∧ ∀m : ℕ, ∀d : ℂ, ∀T : Config (2*m+1)→ℂ,
      ∀v : Config (2*m+1), AnalyticAt ℂ T v → ‖T v‖<r →
      (∀i, ‖d+v i‖<r) → AnalyticAt ℂ (poleResidue B rootB phi hphi d T) v := by
  obtain ⟨a,ha,hjoint⟩ := local_density_phase_joint_analytic B rootB phi hphi hB hr
  obtain ⟨b,c,hb,hc,hslope⟩ := poleParameterDerivative_uniform_lower B phi hphi hB hBn
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro m d T v hT ht hv
  obtain ⟨hN,hF⟩ := hjoint m d (T v) v (ht.trans_le (min_le_left _ _))
    (fun i => (hv i).trans_le (min_le_left _ _))
  have hD := poleParameterDerivative_joint_analyticAt B phi hphi d (T v) v hF
  have hg : AnalyticAt ℂ (fun w => (w,T w)) v := analyticAt_id.prod hT
  have hn : 2*m+1≠0 := by omega
  have hbnd := hslope (2*m+1) hn d (T v) v (ht.trans_le (min_le_right _ _))
    (fun i => (hv i).trans_le (min_le_right _ _))
  have hDn : poleParameterDerivative B phi hphi d (T v) v≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le (mul_pos hc (by positivity)) hbnd)
  have hNc : AnalyticAt ℂ (fun w => formFactorNumerator B rootB phi hphi d (T w) w) v :=
    hN.comp_of_eq (f := fun w : Config (2*m+1) => (w,T w)) hg rfl
  have hDc : AnalyticAt ℂ (fun w => poleParameterDerivative B phi hphi d (T w) w) v :=
    hD.comp_of_eq (f := fun w : Config (2*m+1) => (w,T w)) hg rfl
  exact (analyticAt_const.mul hNc).div hDc hDn

end IsingBulk.Anisotropic.NegativeCycles
