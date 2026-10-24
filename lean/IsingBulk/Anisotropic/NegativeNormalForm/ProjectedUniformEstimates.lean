import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedExtension
import IsingBulk.Anisotropic.NegativeNormalForm.Symmetry

/-! Dimension-free estimates for the actual mean-preserving projected map.
The scalar error estimates needed to instantiate these lemmas remain separate. -/
noncomputable section
open Set Metric
namespace IsingBulk.Anisotropic.NegativeNormalForm

 theorem norm_project_sub_le {n : ℕ} (hn : n ≠ 0) (v w : Config n) :
    ‖project v-project w‖≤2*‖v-w‖ := by
  have he : project v-project w=project (v-w) := by
    simp only [← projectCLM_apply,map_sub]
  rw [he]
  exact norm_project_le hn _

 theorem projectedExtension_error {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n) (v : Config n) :
    projectedExtension U v-v=project (U (project v)-project v) := by
  have hm : mean (U (project v)-project v)=mean (U (project v)) := by
    rw [← meanCLM_apply,map_sub,meanCLM_apply,meanCLM_apply,mean_project_zero hn,sub_zero]
  ext i
  simp only [projectedExtension,projectCLM_apply,Pi.sub_apply,Pi.add_apply]
  change (U (project v) i-mean (U (project v)))+meanCLM n v-v i =
    (U (project v) i-project v i)-mean (U (project v)-project v)
  rw [hm,meanCLM_apply]
  simp only [project]
  ring

 theorem projectedExtension_error_norm {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n) (v : Config n) :
    ‖projectedExtension U v-v‖≤2*‖U (project v)-project v‖ := by
  rw [projectedExtension_error hn]
  exact norm_project_le hn _

 theorem projectedExtension_error_lipschitz {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n)
    (r : ℝ) (c : NNReal)
    (hU : LipschitzOnWith c (fun v => U v-v) (closedBall 0 (2*r) ∩ {v | ZeroMean v})) :
    LipschitzOnWith (4*c) (fun v => projectedExtension U v-v) (closedBall 0 r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  have hp (x : Config n) (hx : x ∈ closedBall 0 r) :
      project x ∈ closedBall 0 (2*r) ∩ {v | ZeroMean v} := by
    refine ⟨?_,project_zeroMean hn x⟩
    simp only [mem_closedBall,dist_zero_right] at hx ⊢
    exact (norm_project_le hn x).trans (mul_le_mul_of_nonneg_left hx (by norm_num))
  have h := hU.dist_le_mul (project v) (hp v hv) (project w) (hp w hw)
  rw [dist_eq_norm,dist_eq_norm] at h
  simp only [dist_eq_norm,projectedExtension_error hn,NNReal.coe_mul,NNReal.coe_ofNat]
  calc
    _ ≤ 2*‖(U (project v)-project v)-(U (project w)-project w)‖ := norm_project_sub_le hn _ _
    _ ≤ 2*((c:ℝ)*‖project v-project w‖) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 2*((c:ℝ)*(2*‖v-w‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_project_sub_le hn v w) c.coe_nonneg) (by norm_num)
    _ = _ := by ring

@[simp] theorem norm_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (v : Config n) :
    ‖permute e v‖=‖v‖ := by
  have hle (f : Equiv.Perm (Fin n)) (w : Config n) : ‖permute f w‖≤‖w‖ := by
    apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr
    intro i
    exact norm_le_pi_norm w (f i)
  apply le_antisymm (hle e v)
  have h := hle e.symm (permute e v)
  simpa [permute,Function.comp_def] using h

end IsingBulk.Anisotropic.NegativeNormalForm
