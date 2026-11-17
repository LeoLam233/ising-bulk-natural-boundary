import IsingBulk.AnisoF002.Geometry.ProfileAnalytic

/-!
# Isolated intersections of the actual endpoint profiles

F002 lemma 2.3 (lem:profile-discrete), using exactly the paper's global
real-analytic signed difference E = R^2-U^2.  Nontriviality has a direct
first-tip witness: for lam < 1, R vanishes and U is positive at pi/2;
for lam > 1, U vanishes and R is positive at pi/(2 lam).  This replaces
only the paper's Taylor computation for the same nontriviality premise.
The target and the globally analytic exceptional set are unchanged.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open Filter Set
open scoped Topology

theorem profileDifference_ne_zero_at_first_tip {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) :
    profileDifferenceF002 lam (highStripWidthF002 lam) ≠ 0 := by
  have hb := highStripWidth_bounds hlam
  by_cases hl : lam < 1
  · have hY : highStripWidthF002 lam = Real.pi / 2 := by
      simp only [highStripWidthF002, max_eq_left hl.le, mul_one]
    have hc1 : Real.cos (highStripWidthF002 lam) = 0 := by
      rw [hY, Real.cos_pi_div_two]
    have hly : 0 < lam * highStripWidthF002 lam := mul_pos hlam hb.1
    have hlu : lam * highStripWidthF002 lam < Real.pi / 2 := by
      rw [hY]
      nlinarith [Real.pi_pos]
    have hc2 : 0 < Real.cos (lam * highStripWidthF002 lam) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hlu⟩
    have hq := profileQInv_strictMono hlam hc2
    rw [profileQInv_zero hlam] at hq
    unfold profileDifferenceF002 signedProfileRF002 signedProfileUF002
    rw [hc1, profilePInv_zero hlam, zero_pow (by decide : 2 ≠ 0), zero_sub]
    exact neg_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt hq))
  · have hl' : 1 < lam := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hne)
    have hly : lam * highStripWidthF002 lam = Real.pi / 2 := by
      unfold highStripWidthF002
      rw [max_eq_right hl'.le]
      field_simp
    have hyu : highStripWidthF002 lam < Real.pi / 2 := by nlinarith
    have hc1 : 0 < Real.cos (highStripWidthF002 lam) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hyu⟩
    have hc2 : Real.cos (lam * highStripWidthF002 lam) = 0 := by
      rw [hly, Real.cos_pi_div_two]
    have hp := profilePInv_strictMono hlam hc1
    rw [profilePInv_zero hlam] at hp
    unfold profileDifferenceF002 signedProfileRF002 signedProfileUF002
    rw [hc2, profileQInv_zero hlam, zero_pow (by decide : 2 ≠ 0), sub_zero]
    exact pow_ne_zero 2 (ne_of_gt hp)

theorem profileDifference_analyticOnNhd {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℝ (profileDifferenceF002 lam) Set.univ :=
  fun y _ => profileDifference_analyticAt hlam y

/-- The complete signed-profile exceptional set has no accumulation at
any finite real height, including simultaneous cosine zeros. -/
theorem profileDifference_locally_nonzero {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) (y : ℝ) :
    ∀ᶠ t in 𝓝[≠] y, profileDifferenceF002 lam t ≠ 0 := by
  rcases (profileDifference_analyticAt hlam y).eventually_eq_zero_or_eventually_ne_zero
      with hzero | hnonzero
  · have hall := (profileDifference_analyticOnNhd hlam).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ y) hzero
    exact False.elim (profileDifference_ne_zero_at_first_tip hlam hne
      (hall (Set.mem_univ (highStripWidthF002 lam))))
  · exact hnonzero

theorem profileDifference_zero_set_closed {lam : ℝ} (hlam : 0 < lam) :
    IsClosed {y : ℝ | profileDifferenceF002 lam y = 0} := by
  apply isClosed_eq _ continuous_const
  exact continuous_iff_continuousAt.mpr (fun y => (profileDifference_analyticAt hlam y).continuousAt)

end
end IsingBulk.AnisoF002.Geometry
