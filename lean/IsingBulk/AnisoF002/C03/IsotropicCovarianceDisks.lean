import IsingBulk.AnisoF002.C03.IsotropicCovariancePrimitives

/-!
# Variance-protected disks and complete joint covariance jets

The actual filled covariance field is controlled on an explicit complex
ball whose radius depends on the proved positive variance. This gives
uniform polynomial particle costs away from total equality, without
excluding any proper partial diagonal. The sharper shell radius remains
a separate refinement using the branch scale estimates.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem singleCoordinate_norm_sub_le {N : ℕ} (p q : ℂ × (Fin N → ℂ)) (i : Fin N) :
    ‖(p.1, p.2 i) - (q.1, q.2 i)‖ ≤ ‖p - q‖ := by
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  exact max_le_max le_rfl (norm_le_pi_norm (p.2 - q.2) i)

def covarianceProtectedRadius (r C d : ℝ) (N : ℕ) : ℝ :=
  min (r / 2) (d / (8 * C ^ 2 * (N : ℝ) ^ 2))

theorem covarianceProtectedRadius_pos {r C d : ℝ} {N : ℕ}
    (hr : 0 < r) (hC : 0 < C) (hd : 0 < d) (hN : 0 < N) :
    0 < covarianceProtectedRadius r C d N := by
  unfold covarianceProtectedRadius
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- The complete field and every fixed total joint derivative are
bounded on a genuinely protected complex ball. The variance lower
bound is supplied numerically here and is discharged on actual images
by the contour coercivity theorem. -/
theorem exists_right_covariance_protected_disks (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r C : ℝ, 0 < r ∧ 1 ≤ C ∧
      ∀ (N : ℕ), 0 < N → ∀ q ∈ rightProductDomain S (r / 2) N,
      ∀ d : ℝ, 0 < d →
        d ≤ (pairVariance (fun i => explicitRightInverse (q.1, q.2 i))).re →
        (∀ p ∈ ball q (covarianceProtectedRadius r C d N),
          AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) p ∧
          d / 2 ≤ ‖pairVariance (fun i => explicitRightInverse (p.1, p.2 i))‖ ∧
          ‖rightCovarianceField p.1 p.2‖ ≤ 2 * C ^ 2 * (N : ℝ) ^ 2 / d) ∧
        ∀ k : ℕ,
          ‖iteratedFDeriv ℂ k (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) q‖ ≤
            protectedJetConstant k (covarianceProtectedRadius r C d N) *
              (2 * C ^ 2 * (N : ℝ) ^ 2 / d) := by
  obtain ⟨r, C, hr, hC, hU, hfirst, hsecond, hsecond_ne, hUb, hPb, hHb, hLip⟩ :=
    exists_right_covariance_primitive_control S hS
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨r, C, hr, hC, ?_⟩
  intro N hN q hq d hd hD
  let ρ := covarianceProtectedRadius r C d N
  have hρ : 0 < ρ := covarianceProtectedRadius_pos hr hCpos hd hN
  have hρ1 : ρ ≤ r / 2 := min_le_left _ _
  have hρ2 : ρ ≤ d / (8 * C ^ 2 * (N : ℝ) ^ 2) := min_le_right _ _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcoef : 0 < 8 * C ^ 2 * (N : ℝ) ^ 2 := by positivity
  have hρcost : 4 * C ^ 2 * (N : ℝ) ^ 2 * ρ ≤ d / 2 := by
    have h := (le_div_iff₀ hcoef).mp hρ2
    nlinarith
  have hq' : q ∈ rightProductDomain S r N :=
    rightProductDomain_mono S (by linarith : r / 2 ≤ r) N hq
  have hball : ball q ρ ⊆ rightProductDomain S r N :=
    (ball_subset_ball hρ1).trans (rightProductDomain_half_ball_subset S r N q hq)
  have hqsingle (i : Fin N) : (q.1, q.2 i) ∈ thickening r (rightParameterSegment S) :=
    rightSingle_of_thickening hq'.1 (hq'.2 i)
  have hall : ∀ p ∈ ball q ρ,
      AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) p ∧
      d / 2 ≤ ‖pairVariance (fun i => explicitRightInverse (p.1, p.2 i))‖ ∧
      ‖rightCovarianceField p.1 p.2‖ ≤ 2 * C ^ 2 * (N : ℝ) ^ 2 / d := by
    intro p hp
    have hp' := hball hp
    have hpsingle (i : Fin N) : (p.1, p.2 i) ∈ thickening r (rightParameterSegment S) :=
      rightSingle_of_thickening hp'.1 (hp'.2 i)
    have hppair (i j : Fin N) : (p.1, p.2 i, p.2 j) ∈
        cthickening r (rightPairParameterSegment S) :=
      thickening_subset_cthickening r _ (rightPair_of_thickening hp'.1 (hp'.2 i) (hp'.2 j))
    have hmove (i : Fin N) :
        ‖explicitRightInverse (p.1, p.2 i) - explicitRightInverse (q.1, q.2 i)‖ ≤ C * ρ := by
      apply (hLip _ (hqsingle i) _ (hpsingle i)).trans
      apply mul_le_mul_of_nonneg_left _ hCpos.le
      have hpn : ‖p - q‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hp
      exact (singleCoordinate_norm_sub_le p q i).trans hpn.le
    have hvariance := pairVariance_lipschitz_bound
      (fun i => explicitRightInverse (q.1, q.2 i)) (fun i => explicitRightInverse (p.1, p.2 i)) C ρ
      hCpos.le hρ.le (fun i => hUb _ (thickening_subset_cthickening r _ (hqsingle i)))
      (fun i => hUb _ (thickening_subset_cthickening r _ (hpsingle i))) hmove
    have hcenter : d ≤ ‖pairVariance (fun i => explicitRightInverse (q.1, q.2 i))‖ :=
      hD.trans (Complex.re_le_norm _)
    have htriangle := norm_le_norm_sub_add
      (pairVariance (fun i => explicitRightInverse (q.1, q.2 i)))
      (pairVariance (fun i => explicitRightInverse (p.1, p.2 i)))
    rw [norm_sub_rev] at htriangle
    have hlower : d / 2 ≤ ‖pairVariance (fun i => explicitRightInverse (p.1, p.2 i))‖ := by
      linarith
    have hne : pairVariance (fun i => explicitRightInverse (p.1, p.2 i)) ≠ 0 :=
      norm_pos_iff.mp ((half_pos hd).trans_le hlower)
    refine ⟨rightCovarianceField_analyticAt p
      (fun i => hU _ (thickening_subset_cthickening r _ (hpsingle i)))
      (fun i j => hfirst _ (hppair i j)) (fun i j => hsecond _ (hppair i j))
      (fun i j => hsecond_ne _ (hppair i j)) hne, hlower, ?_⟩
    have hb := rightCovarianceField_norm_bound p C (d / 2) hCpos.le (half_pos hd)
      (fun i => hPb _ (thickening_subset_cthickening r _ (hpsingle i)))
      (fun i j => hHb _ (hppair i j)) hlower
    exact hb.trans_eq (by ring)
  refine ⟨hall, ?_⟩
  intro k
  exact analytic_ball_joint_jet_bound k
    (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) q ρ
    (2 * C ^ 2 * (N : ℝ) ^ 2 / d) hρ
    (fun p hp => (hall p hp).1) (fun p hp => (hall p hp).2.2)

end IsingBulk.AnisoF002.Isotropic
