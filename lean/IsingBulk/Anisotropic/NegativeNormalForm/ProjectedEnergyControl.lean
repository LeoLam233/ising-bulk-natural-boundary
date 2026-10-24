import IsingBulk.Anisotropic.NegativeNormalForm.HermitianProjection

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem absoluteEnergy_add_le {n : ℕ} (v w : Config n) :
    absoluteEnergy (v+w)≤2*absoluteEnergy v+2*absoluteEnergy w := by
  unfold absoluteEnergy
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h : ‖v i+w i‖^2≤(‖v i‖+‖w i‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  change ‖v i+w i‖^2≤_
  nlinarith [sq_nonneg (‖v i‖-‖w i‖)]

theorem projected_inverse_energy_control {n : ℕ} (hn : n≠0)
    (S v w : Config n) (ε : ℝ) (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hv : ZeroMean v) (hP : project (fun i => v i*S i)=w)
    (hS : ∀ i, ‖S i-1‖≤ε) :
    absoluteEnergy (v-w)≤ε^2*absoluteEnergy v ∧ absoluteEnergy v≤4*absoluteEnergy w := by
  have hpv : project v=v := by
    ext i
    simp only [project,mean,show (∑ i,v i)=0 from hv,zero_div,sub_zero]
  have he : project (fun i => v i*(1-S i))=v-w := by
    have hh : (fun i => v i*(1-S i))=v-(fun i => v i*S i) := by ext i; simp only [Pi.sub_apply]; ring
    rw [hh,← projectCLM_apply,map_sub,projectCLM_apply,projectCLM_apply,hpv,hP]
  have hb : absoluteEnergy (fun i => v i*(1-S i))≤ε^2*absoluteEnergy v := by
    unfold absoluteEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    have hi : ‖v i‖*‖1-S i‖≤ε*‖v i‖ := by
      rw [mul_comm ε]
      exact mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hS i) (norm_nonneg _)
    exact (pow_le_pow_left₀ (by positivity) hi 2).trans_eq (by ring)
  have herr : absoluteEnergy (v-w)≤ε^2*absoluteEnergy v := by
    rw [← he]
    exact (absoluteEnergy_project_le hn _).trans hb
  refine ⟨herr,?_⟩
  have hsmall : ε^2*absoluteEnergy v≤(1/4)*absoluteEnergy v :=
    mul_le_mul_of_nonneg_right (by nlinarith) (absoluteEnergy_nonneg v)
  have ha := absoluteEnergy_add_le w (v-w)
  rw [add_sub_cancel] at ha
  linarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
