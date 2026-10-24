import IsingBulk.Anisotropic.Geometry.IsotropicDomains
import IsingBulk.Anisotropic.Geometry.BoundaryProfiles

namespace IsingBulk.Anisotropic
noncomputable section

theorem cosh_zero_of_axis_cos_zero {z : ℂ} (hr : z.re = 0) (hc : Real.cos z.im = 0) :
    Complex.cosh z = 0 := by
  conv_lhs => rw [← Complex.re_add_im z, hr]
  simp only [Complex.ofReal_zero, zero_add, Complex.cosh_mul_I]
  rw [← Complex.ofReal_cos, hc, Complex.ofReal_zero]

theorem closure_omegaH_one_bounds {z : ℂ} (hz : z ∈ closure (omegaH 1)) :
    |z.im| ≤ Real.pi/2 ∧ ‖Complex.sinh z‖ ≤ 1 := by
  have hs : closure (omegaH 1) ⊆
      {w : ℂ | |w.im| ≤ Real.pi/2 ∧ ‖Complex.sinh w‖ ≤ 1} := by
    apply closure_minimal
    · intro w hw
      obtain ⟨hi,hn⟩ := (mem_omegaH_one_iff w).mp hw
      exact ⟨hi.le, hn.le⟩
    · exact (isClosed_le Complex.continuous_im.abs continuous_const).inter
        (isClosed_le (Complex.continuous_sinh.norm) continuous_const)
  exact hs hz

theorem axis_tip_critical {z : ℂ} (hi : |z.im| = Real.pi/2)
    (hn : ‖Complex.sinh z‖ ≤ 1) : Complex.cosh z = 0 := by
  have hc : Real.cos z.im = 0 := by rw [← Real.cos_abs, hi, Real.cos_pi_div_two]
  have ht := Real.sin_sq_add_cos_sq z.im
  rw [hc] at ht
  have hsq := norm_sinh_sq z
  have hnonneg := norm_nonneg (Complex.sinh z)
  have hzero : Real.sinh z.re = 0 := by nlinarith [sq_nonneg (Real.sinh z.re)]
  exact cosh_zero_of_axis_cos_zero (Real.sinh_eq_zero.mp hzero) hc

theorem frontier_omegaH_one_norm {z : ℂ} (hz : z ∈ frontier (omegaH 1)) :
    ‖Complex.sinh z‖ = 1 := by
  have hb := closure_omegaH_one_bounds (frontier_subset_closure hz)
  have hnot : z ∉ omegaH 1 := by
    rw [(omegaH_isOpen (by norm_num : (0:ℝ)<1)).frontier_eq] at hz
    exact hz.2
  apply le_antisymm hb.2
  by_contra h
  have hn : ‖Complex.sinh z‖ < 1 := lt_of_not_ge h
  have hi : |z.im| < Real.pi/2 := by
    by_contra hh
    have hie : |z.im| = Real.pi/2 := le_antisymm hb.1 (le_of_not_gt hh)
    have hc : Real.cos z.im = 0 := by rw [← Real.cos_abs, hie, Real.cos_pi_div_two]
    have ht := Real.sin_sq_add_cos_sq z.im
    have hs := norm_sinh_sq z
    rw [hc] at ht
    nlinarith [sq_nonneg (Real.sinh z.re), norm_nonneg (Complex.sinh z)]
  exact hnot ((mem_omegaH_one_iff z).mpr ⟨hi, hn⟩)

theorem frontier_omegaH_one_noncritical_im {z : ℂ} (hz : z ∈ frontier (omegaH 1))
    (hc : Complex.cosh z ≠ 0) : |z.im| < Real.pi/2 := by
  have hb := closure_omegaH_one_bounds (frontier_subset_closure hz)
  apply lt_of_le_of_ne hb.1
  intro heq
  exact hc (axis_tip_critical heq hb.2)

theorem frontier_omegaL_one_norm {z : ℂ} (hz : z ∈ frontier (omegaL 1)) :
    ‖Complex.sinh z‖ = 1 := by
  have hr := (mem_frontier_omegaL_iff (by norm_num : (0:ℝ)<1) z).mp hz
  rw [sliceL_isotropic] at hr
  have hsin : Real.sinh z.re = |Real.cos z.im| := by rw [hr, Real.sinh_arsinh]
  have hsq := norm_sinh_sq z
  rw [hsin, sq_abs] at hsq
  have ht := Real.sin_sq_add_cos_sq z.im
  nlinarith [norm_nonneg (Complex.sinh z)]

theorem frontier_omegaL_one_noncritical_re {z : ℂ} (hz : z ∈ frontier (omegaL 1))
    (hc : Complex.cosh z ≠ 0) : 0 < z.re := by
  have hr := (mem_frontier_omegaL_iff (by norm_num : (0:ℝ)<1) z).mp hz
  have hnonneg : 0 ≤ z.re := by rw [hr]; exact sliceL_nonneg (by norm_num) z.im
  apply lt_of_le_of_ne hnonneg
  intro heq
  have hzre : z.re = 0 := heq.symm
  rw [sliceL_isotropic, hzre] at hr
  have hcos : Real.cos z.im = 0 := by
    have h := congrArg Real.sinh hr
    simp only [Real.sinh_zero, Real.sinh_arsinh] at h
    exact abs_eq_zero.mp h.symm
  exact hc (cosh_zero_of_axis_cos_zero hzre hcos)

end
end IsingBulk.Anisotropic
