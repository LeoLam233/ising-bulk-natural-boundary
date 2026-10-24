import IsingBulk.Anisotropic.NegativeNormalForm.ScalarNormalForm
import IsingBulk.Anisotropic.NegativeNormalForm.PoleAverage
import IsingBulk.First.CompactAnalyticShapeIntegral

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.First Set Filter Metric
open scoped Topology

def phaseParameterSlope (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (p : ℂ × ℂ) : ℂ :=
  jointParameterJet (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) 1 p

@[simp] theorem phaseParameterSlope_eq (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (t d : ℂ) :
    phaseParameterSlope B phi hphi (t,d)=deriv (fun z => negativePhase B phi hphi z d) t := by
  simp only [phaseParameterSlope,jointParameterJet_eq,Function.iterate_one]

theorem phaseParameterSlope_origin (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    phaseParameterSlope B phi hphi (0,0)=centralParameterSlope B phi 0 := by
  rw [phaseParameterSlope_eq]
  have hh := negativePhase_hasDerivAt_center B phi hphi 0 (deriv B 0)
    (show HasDerivAt B (deriv B 0) (1-Complex.cos 0) by simpa using hB.differentiableAt.hasDerivAt)
  simpa [centralParameterSlope] using hh.deriv

theorem negativePhase_uniform_slope (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ r : ℝ, 0<r ∧ ∀ t d : ℂ, ‖t‖<r → ‖d‖<r →
      AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d) ∧
      ‖phaseParameterSlope B phi hphi (t,d)-centralParameterSlope B phi 0‖≤
        ‖centralParameterSlope B phi 0‖/4 := by
  have ha : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (0,0) := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  have hj : AnalyticAt ℂ (phaseParameterSlope B phi hphi) (0,0) := jointParameterJet_analyticAt ha 1
  have hc : centralParameterSlope B phi 0≠0 :=
    centralParameterSlope_ne_zero B phi hphi 0 (by simpa using hB0)
  have he : ∀ᶠ p in 𝓝 ((0:ℂ),(0:ℂ)),
      ‖phaseParameterSlope B phi hphi p-centralParameterSlope B phi 0‖<‖centralParameterSlope B phi 0‖/4 :=
    (hj.continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const
      (by simp only [Pi.sub_apply]; rw [phaseParameterSlope_origin B phi hphi hB,sub_self,norm_zero]; exact div_pos (norm_pos_iff.mpr hc) (by norm_num))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (ha.eventually_analyticAt.and he)
  refine ⟨r,hr,?_⟩
  intro t d ht hd
  have hh := hball (show (t,d)∈ball ((0:ℂ),(0:ℂ)) r by
    simpa only [mem_ball,Prod.dist_eq,dist_zero_right,max_lt_iff] using And.intro ht hd)
  exact ⟨hh.1,hh.2.le⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
