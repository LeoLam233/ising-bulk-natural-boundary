import IsingBulk.Anisotropic.NegativeNormalForm.UniformRootBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

theorem phaseRootEnergy_center_lipschitz (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ d t : ℂ, ‖d‖<r → ‖t‖<r →
      ‖Complex.sqrt (phaseEnergy B phi hphi d t 0)-1‖≤L*‖t-(1-Complex.cos d)‖ := by
  obtain ⟨a,L,ha,hL,_hsmall,hLip⟩ := phaseRootEnergy_uniform_small B phi hphi hB hBn 1 zero_lt_one
  have htau : Tendsto (fun d : ℂ => 1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  have hev : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<a ∧
      AnalyticAt ℂ B (1-Complex.cos d) ∧ B (1-Complex.cos d)≠0 ∧ centralHessian B phi d≠0 := by
    filter_upwards [htau.eventually (ball_mem_nhds (0:ℂ) ha),
      htau.eventually hB.eventually_analyticAt,htau.eventually (hB.continuousAt.eventually_ne hBn),
      centralHessian_eventually_nonzero B phi hB] with d ht hb hn hh
    exact ⟨by simpa using ht,hb,hn,hh⟩
  obtain ⟨b,hb,hbs⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min a b,L,lt_min ha hb,hL,?_⟩
  intro d t hd ht
  have hda := hd.trans_le (min_le_left _ _)
  have hta := ht.trans_le (min_le_left _ _)
  obtain ⟨htau,hBa,hBn',hH⟩ := hbs (by simpa using hd.trans_le (min_le_right _ _))
  have hp : ‖(t,(d,(0:ℂ)))‖<a := max_lt hta (max_lt hda (by simpa using ha))
  have hq : ‖(1-Complex.cos d,(d,(0:ℂ)))‖<a := max_lt htau (max_lt hda (by simpa using ha))
  have hh := hLip (t,(d,0)) (1-Complex.cos d,(d,0)) hp hq
  have hcenter : Complex.sqrt (phaseEnergy B phi hphi d (1-Complex.cos d) 0)=1 := by
    simpa using congrArg Complex.sqrt (phaseEnergy_center B phi hphi d hBa hBn' hH)
  rw [hcenter] at hh
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_self,
    max_eq_left (norm_nonneg _)] using hh

end
end IsingBulk.Anisotropic.NegativeNormalForm
