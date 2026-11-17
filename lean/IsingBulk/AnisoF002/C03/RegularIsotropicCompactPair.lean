import IsingBulk.AnisoF002.C03.RegularIsotropicPairGap

/-!
# A uniform pair gap when one lower-half-disk root is away from both endpoints

The only zero of the reciprocal pair denominator in this compact
configuration forces equal endpoint roots. Excluding the actual two
endpoints at one named coordinate supplies a uniform positive gap.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology

theorem exists_lower_disk_pair_gap_away_endpoints (c : ℝ) (hc : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ r s : ℂ,
      ‖r‖ ≤ 1 → ‖s‖ ≤ 1 → r.im ≤ 0 → s.im ≤ 0 →
      c ≤ ‖1 - r‖ → c ≤ ‖1 + r‖ → d ≤ ‖1 - r * s‖ := by
  let K : Set (ℂ × ℂ) := {p | ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 ∧ p.1.im ≤ 0 ∧
    p.2.im ≤ 0 ∧ c ≤ ‖1 - p.1‖ ∧ c ≤ ‖1 + p.1‖}
  have hclosed : IsClosed K := by
    apply IsClosed.inter (isClosed_le continuous_fst.norm continuous_const)
    apply IsClosed.inter (isClosed_le continuous_snd.norm continuous_const)
    apply IsClosed.inter (isClosed_le (Complex.continuous_im.comp continuous_fst) continuous_const)
    apply IsClosed.inter (isClosed_le (Complex.continuous_im.comp continuous_snd) continuous_const)
    exact (isClosed_le continuous_const (continuous_const.sub continuous_fst).norm).inter
      (isClosed_le continuous_const (continuous_const.add continuous_fst).norm)
  have hK : IsCompact K :=
    ((isCompact_closedBall (0 : ℂ) 1).prod (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
      hclosed (by
        intro p hp
        exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hp.1,
          by simpa only [mem_closedBall, dist_zero_right] using hp.2.1⟩)
  have hnz (p : ℂ × ℂ) (hp : p ∈ K) : 0 < ‖1 - p.1 * p.2‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have he := schur_denominator_zero_forces_equal p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hz
    have hsq : p.1 ^ 2 = 1 := by
      rw [← he, ← pow_two] at hz
      exact (sub_eq_zero.mp hz).symm
    rcases sq_eq_one_iff.mp hsq with hp1 | hpm
    · have h := hp.2.2.2.2.1
      rw [hp1, sub_self, norm_zero] at h
      linarith
    · have h := hp.2.2.2.2.2
      rw [hpm, add_neg_cancel, norm_zero] at h
      linarith
  obtain ⟨d, hd, hbound⟩ := hK.exists_forall_le'
    (f := fun p : ℂ × ℂ => ‖1 - p.1 * p.2‖)
    ((continuous_const.sub (continuous_fst.mul continuous_snd)).norm.continuousOn) hnz
  exact ⟨d, hd, fun r s hr hs hri hsi hm hp => hbound (r, s) ⟨hr, hs, hri, hsi, hm, hp⟩⟩

theorem reciprocal_root_distance_neg_one_sq {W r : ℂ}
    (hp : r ^ 2 - 2 * W * r + 1 = 0) :
    ‖1 + r‖ ^ 2 = 2 * ‖W + 1‖ * ‖r‖ := by
  have he : (1 + r) ^ 2 = 2 * (W + 1) * r := by linear_combination hp
  have hn := congrArg norm he
  simpa only [norm_pow, norm_mul, Complex.norm_two] using hn

end
end IsingBulk.AnisoF002.Isotropic
