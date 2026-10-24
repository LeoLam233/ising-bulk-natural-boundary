import IsingBulk.Anisotropic.NegativeNormalForm.ScalarQuadraticControl

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology
set_option maxHeartbeats 800000

 theorem analytic_uniform_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} (hf : AnalyticAt ℂ f 0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧
      (∀ p : E, ‖p‖<r → AnalyticAt ℂ f p) ∧
      (∀ p q : E, ‖p‖<r → ‖q‖<r → ‖f p-f q‖≤L*‖p-q‖) := by
  obtain ⟨L,s,hs,hL⟩ := (hf.contDiffAt (n := 1)).exists_lipschitzOnWith
  have he : ∀ᶠ p : E in 𝓝 0, p∈s ∧ AnalyticAt ℂ f p := by
    filter_upwards [hs,hf.eventually_analyticAt] with p hp ha using ⟨hp,ha⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r,(L:ℝ)+1,hr,by positivity,?_,?_⟩
  · intro p hp
    exact (hball (show p∈ball (0:E) r by simpa using hp)).2
  · intro p q hp hq
    have hp' := (hball (show p∈ball (0:E) r by simpa using hp)).1
    have hq' := (hball (show q∈ball (0:E) r by simpa using hq)).1
    have hh := hL.dist_le_mul p hp' q hq'
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- Actual analytic moving-coordinate slope, with the increment as the last coordinate. -/
def scalarPairSlope (S : ScalarTriple → ℂ) : ScalarTriple × ℂ → ℂ :=
  coordinateHadamard (fun p => S (p.1.1,(p.1.2.1,p.1.2.2+p.2)))

theorem scalarPairSlope_analyticAt (S : ScalarTriple → ℂ) (ha : AnalyticAt ℂ S 0) :
    AnalyticAt ℂ (scalarPairSlope S) 0 := by
  apply coordinateHadamard_analyticAt
  apply ha.fun_comp_of_eq (f := fun p : ScalarTriple × ℂ => (p.1.1,(p.1.2.1,p.1.2.2+p.2)))
  · exact (analyticAt_fst.comp analyticAt_fst).prod
      (((analyticAt_fst.comp analyticAt_snd).comp analyticAt_fst).prod
        (((analyticAt_snd.comp analyticAt_snd).comp analyticAt_fst).add analyticAt_snd))
  · simp

 theorem scalarPairSlope_even_uniform (S : ScalarTriple → ℂ) (ha : AnalyticAt ℂ S 0)
    (heven : ∀ t v : ℂ, S (t,(0,-v))=S (t,(0,v))) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t d x y : ℂ,
      ‖t‖<r → ‖d‖<r → ‖x‖<r → ‖y‖<r →
      S (t,(d,x))-S (t,(d,y))=(x-y)*scalarPairSlope S ((t,(d,y)),x-y) ∧
      ‖scalarPairSlope S ((t,(d,y)),x-y)‖≤L*(‖d‖+‖x‖+‖y‖) := by
  let f : ScalarTriple × ℂ → ℂ := fun p => S (p.1.1,(p.1.2.1,p.1.2.2+p.2))
  have hf : AnalyticAt ℂ f 0 := by
    apply ha.fun_comp_of_eq (f := fun p : ScalarTriple × ℂ => (p.1.1,(p.1.2.1,p.1.2.2+p.2)))
    · exact (analyticAt_fst.comp analyticAt_fst).prod
        (((analyticAt_fst.comp analyticAt_snd).comp analyticAt_fst).prod
          (((analyticAt_snd.comp analyticAt_snd).comp analyticAt_fst).add analyticAt_snd))
    · simp
  have hq := scalarPairSlope_analyticAt S ha
  have hc : ContinuousAt (fun p : ScalarTriple × ℂ => ((p.1.1,((0:ℂ),(0:ℂ))),(0:ℂ))) 0 := by fun_prop
  have hzero : ∀ᶠ p : ScalarTriple × ℂ in 𝓝 0, scalarPairSlope S ((p.1.1,(0,0)),0)=0 := by
    filter_upwards [hc.tendsto.eventually hf.eventually_analyticAt] with p hp
    change coordinateHadamard f ((p.1.1,(0,0)),0)=0
    rw [coordinateHadamard_at_zero_last]
    have hline : HasDerivAt (fun v : ℂ => ((p.1.1,((0:ℂ),(0:ℂ))),v)) ((0:ScalarTriple),1) 0 :=
      (hasDerivAt_const (0:ℂ) (p.1.1,((0:ℂ),(0:ℂ)))).prodMk (hasDerivAt_id (0:ℂ))
    have hh := hp.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline
    have hd : deriv (fun v => f ((p.1.1,(0,0)),v)) 0=
        fderiv ℂ f ((p.1.1,(0,0)),0) ((0:ScalarTriple),1) := hh.deriv
    exact hd.symm.trans (by simpa [f] using deriv_zero_of_even_complex (fun v => S (p.1.1,(0,v))) (heven p.1.1))
  obtain ⟨r,L,hr,hL,_ha,hLip⟩ := analytic_uniform_lipschitz hq
  obtain ⟨s,hs,hsmall⟩ := Metric.eventually_nhds_iff.mp ((coordinateHadamard_identity hf).and hzero)
  refine ⟨min r s/4,2*L,by positivity,by positivity,?_⟩
  intro t d x y ht hd hx hy
  have hmin : 0<min r s := lt_min hr hs
  let p : ScalarTriple × ℂ := ((t,(d,y)),x-y)
  have hp : ‖p‖<min r s := by
    change max (max ‖t‖ (max ‖d‖ ‖y‖)) ‖x-y‖<min r s
    have hxy := norm_sub_le x y
    exact max_lt (max_lt (by linarith) (max_lt (by linarith) (by linarith))) (by linarith)
  have hpbase : ‖((t,((0:ℂ),(0:ℂ))),(0:ℂ))‖<r := by
    simp only [Prod.norm_def,norm_zero,max_self,max_eq_left (norm_nonneg _)]
    exact (by linarith [min_le_left r s])
  have hsmallp := hsmall (show dist p 0<s by simpa using hp.trans_le (min_le_right _ _))
  constructor
  · simpa [f,p,scalarPairSlope,show y+(x-y)=x by ring] using hsmallp.1
  · have h := hLip p ((t,(0,0)),0) (hp.trans_le (min_le_left _ _)) hpbase
    rw [hsmallp.2,sub_zero] at h
    have hdist : ‖p-((t,(0,0)),0)‖≤2*(‖d‖+‖x‖+‖y‖) := by
      simp only [p,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,sub_zero,norm_zero]
      have hxy := norm_sub_le x y
      exact max_le (max_le (by positivity) (max_le (by nlinarith [norm_nonneg d,norm_nonneg x,norm_nonneg y])
        (by nlinarith [norm_nonneg d,norm_nonneg x,norm_nonneg y]))) (by nlinarith [norm_nonneg d,norm_nonneg x,norm_nonneg y])
    exact (h.trans (mul_le_mul_of_nonneg_left hdist hL.le)).trans_eq (by ring)

end
end IsingBulk.Anisotropic.NegativeNormalForm
