import IsingBulk.Joint.Slices.Collars

namespace IsingBulk.Joint
noncomputable section
open Set Metric
open scoped Topology

theorem disk_hasLocalCollar : HasLocalCollar {s : ℂ | ‖s‖ < 1} := by
  let D : Set ℂ := {s | ‖s‖ < 1}
  have hD : IsOpen D := isOpen_lt continuous_norm continuous_const
  apply hasScalarCollar_of_inward_motion hD
  intro P hP ε hε
  have hn : ‖P‖ ≤ 1 := closure_minimal (fun (z:ℂ) (h:z∈D) => (show ‖z‖ < 1 from h).le)
    (isClosed_le continuous_norm continuous_const) (frontier_subset_closure hP)
  have hc : Continuous (fun t : ℝ => t • P) := by fun_prop
  have hN : (fun t : ℝ => t • P) ⁻¹' ball P ε ∈ 𝓝 (1:ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using isOpen_ball.mem_nhds (mem_ball_self (x:=P) hε)
  have hcl : (1:ℝ) ∈ closure (Ioo 0 1) := by rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]; simp
  obtain ⟨t,htN,ht⟩ := mem_closure_iff_nhds.mp hcl _ hN
  have hnorm : ‖t • P‖ < 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact (mul_le_mul_of_nonneg_left hn ht.1.le).trans_lt (by simpa using ht.2)
  refine ⟨fun Q => t • Q,by fun_prop,⟨hnorm,htN⟩,?_⟩
  intro Q hQ
  have hQt : ‖t • Q‖ < 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg Q) ht.2.le) hQ
  have he : D = ball (0:ℂ) 1 := by ext z; simp [D,dist_eq_norm]
  change t • Q ∈ D at hQt
  rw [he] at hQ hQt ⊢
  exact (convex_ball (0:ℂ) 1).segment_subset hQ hQt

theorem exterior_hasLocalCollar : HasLocalCollar {s : ℂ | 1 < ‖s‖} := by
  let D : Set ℂ := {s | 1 < ‖s‖}
  have hD : IsOpen D := isOpen_lt continuous_const continuous_norm
  apply hasScalarCollar_of_inward_motion hD
  intro P hP ε hε
  have hn : 1 ≤ ‖P‖ := closure_minimal (fun (z:ℂ) (h:z∈D) => (show 1 < ‖z‖ from h).le)
    (isClosed_le continuous_const continuous_norm) (frontier_subset_closure hP)
  have hc : Continuous (fun t : ℝ => t • P) := by fun_prop
  have hN : (fun t : ℝ => t • P) ⁻¹' ball P ε ∈ 𝓝 (1:ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using isOpen_ball.mem_nhds (mem_ball_self (x:=P) hε)
  have hcl : (1:ℝ) ∈ closure (Ioi 1) := by rw [closure_Ioi]; simp
  obtain ⟨t,htN,ht⟩ := mem_closure_iff_nhds.mp hcl _ hN
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hnorm : 1 < ‖t • P‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht0]
    exact ht.trans_le (by nlinarith)
  refine ⟨fun Q => t • Q,by fun_prop,⟨hnorm,htN⟩,?_⟩
  intro Q hQ Z hZ
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hZ
  have he : a • Q+b • (t • Q) = (a+b*t) • Q := by rw [smul_smul,add_smul]
  have hc' : 1 ≤ a+b*t := by
    have ht1 : 1 < t := ht
    nlinarith [mul_nonneg hb (sub_nonneg.mpr ht1.le)]
  change 1 < ‖a • Q+b • (t • Q)‖
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans_le hc')]
  exact lt_of_lt_of_le hQ (le_mul_of_one_le_left (norm_nonneg Q) hc')

end
end IsingBulk.Joint
