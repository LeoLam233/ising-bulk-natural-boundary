import IsingBulk.AnisoF002.C03.IsotropicFirstPlateau

/-!
# The original branch-width choice already supplies the first plateaus

The actual branch and collision angles satisfy alpha<b and sin(b)<2sin(alpha).
Consequently the common tail choice 4eta<=sin(b) is strictly inside both
first-coincidence bump plateaus, without an extra final hypothesis.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

theorem isotropic_first_angle_lt_branch {α b : ℝ}
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) : α < b := by
  have hc : Real.cos α < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hα.2.le hα.1
  by_contra h
  have hh := Real.cos_le_cos_of_nonneg_of_le_pi hb.1.le hα.2.le (le_of_not_gt h)
  linarith

theorem isotropic_first_branch_sine_bound {α b : ℝ}
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) : Real.sin b < 2 * Real.sin α := by
  have hc : Real.cos α < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hα.2.le hα.1
  have hsα := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  have hsqα := Real.sin_sq_add_cos_sq α
  have hsqb := Real.sin_sq_add_cos_sq b
  rw [show Real.cos b = 2 * Real.cos α - 1 by linarith] at hsqb
  nlinarith

theorem isotropic_first_plateau_width {α b η : ℝ}
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hwidth : 4 * η ≤ Real.sin b) :
    2 * η < Real.sin α := by
  linarith [isotropic_first_branch_sine_bound hα hb hpoint]

theorem isotropic_first_physical_branch_geometry {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) :
    0 < rightBranchEndpoint (2 * Real.cos α) ∧
      rightBranchEndpoint (2 * Real.cos α) < Real.pi ∧
      1 + Real.cos (rightBranchEndpoint (2 * Real.cos α)) = 2 * Real.cos α ∧
      α < rightBranchEndpoint (2 * Real.cos α) := by
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hcos := Real.cos_pos_of_mem_Ioo
    (show α ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], hhalf⟩)
  have hcos1 : Real.cos α < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hπ.le hα
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := ⟨by positivity, by linarith⟩
  have hb := And.intro (rightBranchEndpoint_pos _ hS.2) (rightBranchEndpoint_lt_pi _ hS.1)
  have hp : 1 + Real.cos (rightBranchEndpoint (2 * Real.cos α)) = 2 * Real.cos α := by
    rw [rightBranchEndpoint, Real.cos_arccos (by linarith [hS.1]) (by linarith [hS.2])]
    ring
  exact ⟨hb.1, hb.2, hp, isotropic_first_angle_lt_branch ⟨hα, hπ⟩ hb hp⟩

end
end IsingBulk.AnisoF002.Isotropic
