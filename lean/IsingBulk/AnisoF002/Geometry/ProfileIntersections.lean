import IsingBulk.AnisoF002.Geometry.HighComponent
import IsingBulk.AnisoF002.Geometry.ProfileDiscrete

/-!
# The analytic exceptional set is the actual endpoint intersection set

F002 eq:signed-profiles, lemma 2.3, and the graph reduction in proposition
2.4 (prop:regular_dense).  Both signed profiles are the actual inverse
hyperbolic profiles, including their zeros and negative values.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set

theorem profilePInv_neg {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    profilePInvF002 lam (-y) = -profilePInvF002 lam y := by
  apply (profileP_strictMono hlam).injective
  rw [profileP_rightInverse hlam (-y), profileP_neg, profileP_rightInverse hlam y]

theorem profileQInv_neg {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    profileQInvF002 lam (-y) = -profileQInvF002 lam y := by
  apply (profileQ_strictMono hlam).injective
  rw [profileQ_rightInverse hlam (-y), profileQ_neg, profileQ_rightInverse hlam y]

theorem profilePInv_abs {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    profilePInvF002 lam |y| = |profilePInvF002 lam y| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, abs_of_nonneg (profilePInv_nonneg hlam hy)]
  · have hp : profilePInvF002 lam y ≤ 0 := by
      have hh := (profilePInv_strictMono hlam).monotone hy
      simpa only [profilePInv_zero hlam] using hh
    rw [abs_of_nonpos hy, profilePInv_neg hlam, abs_of_nonpos hp]

theorem profileQInv_abs {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    profileQInvF002 lam |y| = |profileQInvF002 lam y| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, abs_of_nonneg (profileQInv_nonneg hlam hy)]
  · have hp : profileQInvF002 lam y ≤ 0 := by
      have hh := (profileQInv_strictMono hlam).monotone hy
      simpa only [profileQInv_zero hlam] using hh
    rw [abs_of_nonpos hy, profileQInv_neg hlam, abs_of_nonpos hp]

theorem lowProfile_eq_signed_max {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    lowProfileF002 lam y = max |signedProfileRF002 lam y| |signedProfileUF002 lam y| := by
  unfold lowProfileF002 signedProfileRF002 signedProfileUF002
  rw [profilePInv_abs hlam, profileQInv_abs hlam]

theorem profileDifference_eq_zero_iff_abs_eq (lam y : ℝ) :
    profileDifferenceF002 lam y = 0 ↔
      |signedProfileRF002 lam y| = |signedProfileUF002 lam y| := by
  rw [profileDifferenceF002, sub_eq_zero, sq_eq_sq_iff_abs_eq_abs]

theorem geometryF1_zero_iff_signed_profile {lam x y : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) : geometryF1 lam x y = 0 ↔ x = |signedProfileRF002 lam y| := by
  have hP0 : 0 ≤ profilePF002 lam x := by
    have hh := (profileP_strictMono hlam).monotone hx
    simpa only [profileP_zero] using hh
  rw [geometryF1_profile_factor, mul_eq_zero]
  have hc : Real.cosh (lam * x) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (Real.cosh_pos _))
  simp only [hc, false_or, sub_eq_zero]
  constructor
  · intro hsq
    have hp : |Real.cos y| = profilePF002 lam x :=
      (sq_eq_sq₀ (abs_nonneg _) hP0).mp (by simpa only [sq_abs] using hsq)
    have hi := congrArg (profilePInvF002 lam) hp
    rw [profileP_leftInverse hlam x, profilePInv_abs hlam] at hi
    exact hi.symm
  · intro hi
    have hx' : x = profilePInvF002 lam |Real.cos y| := by
      rw [profilePInv_abs hlam]
      exact hi
    rw [hx', profileP_rightInverse hlam _, sq_abs]

theorem geometryF2_zero_iff_signed_profile {lam x y : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) : geometryF2 lam x y = 0 ↔ x = |signedProfileUF002 lam y| := by
  have hQ0 : 0 ≤ profileQF002 lam x := by
    have hh := (profileQ_strictMono hlam).monotone hx
    simpa only [profileQ_zero] using hh
  rw [geometryF2_profile_factor, mul_eq_zero]
  have hc : Real.cosh x ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (Real.cosh_pos _))
  simp only [hc, false_or, sub_eq_zero]
  constructor
  · intro hsq
    have hp : |Real.cos (lam * y)| = profileQF002 lam x :=
      (sq_eq_sq₀ (abs_nonneg _) hQ0).mp (by simpa only [sq_abs] using hsq)
    have hi := congrArg (profileQInvF002 lam) hp
    rw [profileQ_leftInverse hlam x, profileQInv_abs hlam] at hi
    exact hi.symm
  · intro hi
    have hx' : x = profileQInvF002 lam |Real.cos (lam * y)| := by
      rw [profileQInv_abs hlam]
      exact hi
    rw [hx', profileQ_rightInverse hlam _, sq_abs]

theorem endpoint_intersection_iff {lam x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    geometryF1 lam x y = 0 ∧ geometryF2 lam x y = 0 ↔
      x = |signedProfileRF002 lam y| ∧ profileDifferenceF002 lam y = 0 := by
  rw [geometryF1_zero_iff_signed_profile hlam hx, geometryF2_zero_iff_signed_profile hlam hx,
    profileDifference_eq_zero_iff_abs_eq]
  constructor
  · rintro ⟨hR, hU⟩
    exact ⟨hR, hR.symm.trans hU⟩
  · rintro ⟨hR, hRU⟩
    exact ⟨hR, hR.trans hRU⟩

theorem geometryF1_abs_re (lam x y : ℝ) : geometryF1 lam |x| y = geometryF1 lam x y := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · delta geometryF1
    simp only [abs_of_nonpos hx, mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq]

theorem geometryF2_abs_re (lam x y : ℝ) : geometryF2 lam |x| y = geometryF2 lam x y := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · delta geometryF2
    simp only [abs_of_nonpos hx, mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq]

theorem endpoint_pair_zero_implies_difference_zero {lam x y : ℝ} (hlam : 0 < lam)
    (hF1 : geometryF1 lam x y = 0) (hF2 : geometryF2 lam x y = 0) :
    profileDifferenceF002 lam y = 0 := by
  have hh : geometryF1 lam |x| y = 0 ∧ geometryF2 lam |x| y = 0 := by
    simpa only [geometryF1_abs_re, geometryF2_abs_re] using And.intro hF1 hF2
  exact ((endpoint_intersection_iff hlam (abs_nonneg x)).mp hh).2

theorem lowProfile_pos_of_difference_ne_zero {lam y : ℝ} (hlam : 0 < lam)
    (hE : profileDifferenceF002 lam y ≠ 0) : 0 < lowProfileF002 lam y := by
  have hn := lowProfile_nonneg hlam y
  apply lt_of_le_of_ne hn
  intro hz
  have hzero : max |signedProfileRF002 lam y| |signedProfileUF002 lam y| = 0 := by
    rw [← lowProfile_eq_signed_max hlam]
    exact hz.symm
  have hR : |signedProfileRF002 lam y| = 0 :=
    le_antisymm (by rw [← hzero]; exact le_max_left _ _) (abs_nonneg _)
  have hU : |signedProfileUF002 lam y| = 0 :=
    le_antisymm (by rw [← hzero]; exact le_max_right _ _) (abs_nonneg _)
  exact hE ((profileDifference_eq_zero_iff_abs_eq lam y).mpr (hR.trans hU.symm))

theorem endpoint_locus_regular_factors {lam : ℝ} {z : ℂ} (hlam : 0 < lam)
    (hZ : z ∈ endpointLocusF002 lam) (hE : profileDifferenceF002 lam z.im ≠ 0) :
    (geometryF1 lam z.re z.im = 0 ∧ geometryF2 lam z.re z.im ≠ 0) ∨
      (geometryF2 lam z.re z.im = 0 ∧ geometryF1 lam z.re z.im ≠ 0) := by
  rcases mul_eq_zero.mp hZ with hF1 | hF2
  · exact Or.inl ⟨hF1, fun hF2 => hE (endpoint_pair_zero_implies_difference_zero hlam hF1 hF2)⟩
  · exact Or.inr ⟨hF2, fun hF1 => hE (endpoint_pair_zero_implies_difference_zero hlam hF1 hF2)⟩

end
end IsingBulk.AnisoF002.Geometry
