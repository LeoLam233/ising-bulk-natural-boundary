import IsingBulk.Anisotropic.NegativeNormalForm.ProjectionLinear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Analytic.Constructions

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology ContDiff

def projectedExtension {n : ℕ} (U : Config n → Config n) (v : Config n) : Config n :=
  projectCLM n (U (projectCLM n v)) + meanVectorCLM n v

theorem mean_project_zero {n : ℕ} (hn : n ≠ 0) (v : Config n) : mean (project v)=0 := by
  unfold mean
  rw [show ∑ i, project v i=0 from project_zeroMean hn v,zero_div]

theorem meanVectorCLM_mean {n : ℕ} (hn : n ≠ 0) (v : Config n) : mean (meanVectorCLM n v)=mean v := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  simp [meanVectorCLM,mean,hn']

theorem projectedExtension_mean {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n) (v : Config n) :
    mean (projectedExtension U v)=mean v := by
  rw [← meanCLM_apply,projectedExtension,map_add,meanCLM_apply,meanCLM_apply,
    projectCLM_apply,mean_project_zero hn,meanVectorCLM_mean hn,zero_add]

theorem mean_eq_zero_iff {n : ℕ} (hn : n ≠ 0) (v : Config n) : mean v=0 ↔ ZeroMean v := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  simp [mean,ZeroMean,hn']

theorem projectedExtension_zeroMean_iff {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n) (v : Config n) :
    ZeroMean (projectedExtension U v) ↔ ZeroMean v := by
  rw [← mean_eq_zero_iff hn,projectedExtension_mean hn,mean_eq_zero_iff hn]

theorem projectedExtension_on_zeroMean {n : ℕ} (U : Config n → Config n) {v : Config n}
    (hv : ZeroMean v) : projectedExtension U v=project (U v) := by
  simp only [projectedExtension,projectCLM_apply,project_eq_self hv]
  have hm : meanVectorCLM n v=0 := by
    ext i
    simp [meanVectorCLM,mean,show ∑ i, v i=0 from hv]
  rw [hm,add_zero]

theorem projectedExtension_zero {n : ℕ} (U : Config n → Config n) (hU : U 0=0) :
    projectedExtension U 0=0 := by
  simp only [projectedExtension,map_zero,hU,add_zero]

theorem projectedExtension_analyticAt {n : ℕ} (U : Config n → Config n) (hU : AnalyticAt ℂ U 0) :
    AnalyticAt ℂ (projectedExtension U) 0 := by
  have hu := hU.comp_of_eq ((projectCLM n).analyticAt 0) (map_zero _)
  exact (((projectCLM n).analyticAt _).comp hu).add ((meanVectorCLM n).analyticAt 0)

theorem projectedExtension_hasFDerivAt {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n)
    (hU : HasFDerivAt U (ContinuousLinearMap.id ℂ (Config n)) 0) :
    HasFDerivAt (projectedExtension U) (ContinuousLinearMap.id ℂ (Config n)) 0 := by
  have hu : HasFDerivAt U (ContinuousLinearMap.id ℂ (Config n)) (projectCLM n 0) := by simpa only [map_zero] using hU
  have hcomp := ((projectCLM n).hasFDerivAt.comp 0 (hu.comp 0 (projectCLM n).hasFDerivAt)).add
    (meanVectorCLM n).hasFDerivAt
  have hlinear : (projectCLM n).comp ((ContinuousLinearMap.id ℂ (Config n)).comp (projectCLM n))+
      meanVectorCLM n = ContinuousLinearMap.id ℂ (Config n) := by
    rw [ContinuousLinearMap.id_comp,projectCLM_idempotent hn]
    simp [projectCLM]
  rw [hlinear] at hcomp
  exact hcomp

/-- The full-space extension preserves mean exactly, so its genuine analytic
inverse restricts to the zero-mean hyperplane. No inverse or normal form is assumed. -/
theorem exists_projected_inverse {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0=0)
    (hdU : HasFDerivAt U (ContinuousLinearMap.id ℂ (Config n)) 0) :
    ∃ V : Config n → Config n,
      AnalyticAt ℂ V 0 ∧ V 0=0 ∧
      HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ᶠ v in 𝓝 (0:Config n), V (projectedExtension U v)=v) ∧
      (∀ᶠ w in 𝓝 (0:Config n), projectedExtension U (V w)=w ∧
        (ZeroMean w → ZeroMean (V w) ∧ project (U (V w))=w)) := by
  let F := projectedExtension U
  have hF : AnalyticAt ℂ F 0 := projectedExtension_analyticAt U hU
  have hF0 : F 0=0 := projectedExtension_zero U hU0
  have hd : HasFDerivAt F (ContinuousLinearEquiv.refl ℂ (Config n) : Config n →L[ℂ] Config n) 0 :=
    projectedExtension_hasFDerivAt hn U hdU
  have hc : ContDiffAt ℂ ω F 0 := hF.contDiffAt
  have hs := hc.hasStrictFDerivAt' hd (by simp)
  let V := hc.localInverse hd (by simp)
  have hV : AnalyticAt ℂ V 0 := by simpa [hF0] using (hc.to_localInverse hd (by simp)).analyticAt
  have hV0 : V 0=0 := by simpa [hF0,V] using hc.localInverse_apply_image hd (by simp)
  have hdV : HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0 := by
    simpa [hF0,V,ContDiffAt.localInverse] using hs.to_localInverse.hasFDerivAt
  refine ⟨V,hV,hV0,hdV,hs.eventually_left_inverse,?_⟩
  have hr : ∀ᶠ w in 𝓝 (0:Config n), F (V w)=w := by simpa [hF0,V,ContDiffAt.localInverse] using hs.eventually_right_inverse
  filter_upwards [hr] with w hw
  refine ⟨hw,fun hmean => ?_⟩
  have hmean' : ZeroMean (V w) := (projectedExtension_zeroMean_iff hn U (V w)).mp (by change ZeroMean (F (V w)); rw [hw]; exact hmean)
  exact ⟨hmean', (projectedExtension_on_zeroMean U hmean').symm.trans hw⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
