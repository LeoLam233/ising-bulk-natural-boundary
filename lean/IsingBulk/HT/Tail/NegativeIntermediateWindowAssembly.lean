import IsingBulk.HT.Tail.SignedOddTailDomination
import IsingBulk.HT.Tail.IntermediateWindowAssembly
import IsingBulk.HT.Tail.NegativeCommonAllSectorParameters
import IsingBulk.Tail.IntermediateWindowAssembly

/-! The literal reflected K/small-S intermediate superseries from
its exhaustive actual signed partition and the common source estimates. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set Filter Asymptotics
open IsingBulk.HT.Contour
open scoped Topology

abbrev negativeIntermediateOddKSNormWindow := signedIntermediateOddKSNormWindow (-1)

/-- The summand of the literal strict intermediate window. -/
def negativeIntermediateOddKSNormWindowTerm (p : ℕ) (d : LocalBranchData) (eta alpha tau : ℝ)
    (j : ℕ) (D eps cut : ℝ) (N : ℕ) : ℝ :=
  if p+2 ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps) then
    signedOriginalKSNorm (-1) N (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau j
      (radialParameter d.theta eps) cut else 0

theorem negativeIntermediateOddKSNormWindowTerm_nonneg (p : ℕ) (d : LocalBranchData)
    (eta alpha tau : ℝ) (j : ℕ) (D eps cut : ℝ) (N : ℕ) :
    0 ≤ negativeIntermediateOddKSNormWindowTerm p d eta alpha tau j D eps cut N := by
  unfold negativeIntermediateOddKSNormWindowTerm
  split_ifs
  · exact signedOriginalKSNorm_nonneg (-1) ..
  · exact le_rfl

theorem negativeIntermediateOddKSNormWindow_eq_tsum (p : ℕ) (d : LocalBranchData)
    (eta alpha tau : ℝ) (j : ℕ) (D eps cut : ℝ) :
    negativeIntermediateOddKSNormWindow p d eta alpha tau j D eps cut =
      ∑' N, negativeIntermediateOddKSNormWindowTerm p d eta alpha tau j D eps cut N := rfl

/-- The mixed/left contribution is left unrestricted. The original
all-branch and compact-right contributions use their proved weak windows. -/
theorem negativeIntermediateOddKSNormWindowTerm_le_sector_windows (p : ℕ) (d : LocalBranchData)
    (eta outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (D : ℝ) (j : ℕ) (eps cut : ℝ)
    (hmajor : ∀ N : ℕ, p+2 ≤ N →
      signedOriginalKSNorm (-1) N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau j (radialParameter d.theta eps) cut ≤
      ‖iteratedDeriv j (signedOriginalSectorIntegral (-1) N (constructedSelector d.thetaB eta d.alpha)
        (Real.exp (-d.c₀*eps)) d.tau d.thetaB outer inner ho hi none)
          (radialParameter d.theta eps)‖ +
      signedMixedLeftSectorNorm (-1) N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau d.thetaB outer inner ho hi j (radialParameter d.theta eps) cut +
      signedRightCompactSectorNorm (-1) N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau d.thetaB outer inner ho hi j (radialParameter d.theta eps) cut)
    (N : ℕ) :
    negativeIntermediateOddKSNormWindowTerm p d eta d.alpha d.tau j D eps cut N ≤
      negativeHTOriginalAllBranchWindowTerm p d eta outer inner ho hi D j eps N +
      signedMixedLeftSectorNorm (-1) N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau d.thetaB outer inner ho hi j (radialParameter d.theta eps) cut +
      htCompactRightWindow p D eps
        (fun N => signedRightCompactSectorNorm (-1) N (constructedSelector d.thetaB eta d.alpha)
          (Real.exp (-d.c₀*eps)) d.tau d.thetaB outer inner ho hi j
            (radialParameter d.theta eps) cut) N := by
  by_cases hwindow : p+2 ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps)
  · have hwide := ht_intermediate_window_subset hwindow
    simpa only [negativeIntermediateOddKSNormWindowTerm,negativeHTOriginalAllBranchWindowTerm,htCompactRightWindow,
      ite_eq_left hwindow,ite_eq_left hwide] using hmajor N hwindow.1
  · rw [negativeIntermediateOddKSNormWindowTerm,ite_eq_right hwindow]
    exact add_nonneg
      (add_nonneg (negativeHTOriginalAllBranchWindowTerm_nonneg ..) (signedMixedLeftSectorNorm_nonneg (-1) ..))
      (htCompactRightWindow_nonneg p D eps (fun N => signedRightCompactSectorNorm_nonneg (-1) ..) N)

/-- The common sector choice controls the exact intermediate summands.
The comparison is obtained from the proved finite sector decomposition;
no norm domination or intermediate-window conclusion is assumed here. -/
theorem negative_ht_common_intermediateOddKSNormWindow_radialSeriesSmall {p order : ℕ}
    {d : LocalBranchData} (cfg : NegativeHTCommonAllSectorParameters p d order)
    (j : ℕ) (hj : j ≤ order) :
    radialSeriesSmall (fun eps N => negativeIntermediateOddKSNormWindowTerm p d cfg.eta d.alpha d.tau
      j cfg.D eps (eps^cfg.beta) N) := by
  have hsectors := ((cfg.allBranch_small j hj).add (cfg.mixedLeft_small j hj)).add
    (cfg.rightCompact_small j hj)
  apply hsectors.of_eventually_le
  · intro eps N
    exact negativeIntermediateOddKSNormWindowTerm_nonneg ..
  · intro eps N
    exact add_nonneg
      (add_nonneg (negativeHTOriginalAllBranchWindowTerm_nonneg ..) (signedMixedLeftSectorNorm_nonneg (-1) ..))
      (htCompactRightWindow_nonneg p cfg.D eps
        (fun N => signedRightCompactSectorNorm_nonneg (-1) ..) N)
  · filter_upwards [radial_source_eventually_damping d cfg.c0_small,
      radial_power_cutoff_eventually cfg.beta_pos (0:ℝ) (show (0:ℝ) < 1 from zero_lt_one)]
      with eps hdomain hcut
    intro N
    apply negativeIntermediateOddKSNormWindowTerm_le_sector_windows p d cfg.eta cfg.outer cfg.inner
      cfg.outer_pos cfg.inner_pos cfg.D j eps (eps^cfg.beta) _ N
    intro M hM
    exact signed_originalKSNorm_le_sectors (-1) (by norm_num) M (by omega)
      (constructedSelector d.thetaB cfg.eta d.alpha) cfg.selector_regular
      hdomain.1 hdomain.2.1 d.tau_pos.le hcut.1 d.thetaB cfg.outer cfg.inner
      cfg.outer_pos cfg.inner_pos j (radialParameter d.theta eps) hdomain.2.2
      (fun q lam => cfg.current_allBranch_zero M q (Real.exp (-d.c₀*eps)) lam j
        (radialParameter d.theta eps))

/-- Little-o for the literal intermediate sum used by
`actual_higher_tail_domination`, retaining the common cutoff power. -/
theorem negative_ht_common_intermediateOddKSNormWindow_littleO {p order : ℕ} {d : LocalBranchData}
    (cfg : NegativeHTCommonAllSectorParameters p d order) (j : ℕ) (hj : j ≤ order) :
    (fun eps : ℝ => negativeIntermediateOddKSNormWindow p d cfg.eta d.alpha d.tau j cfg.D eps
      (eps^cfg.beta)) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  exact (negative_ht_common_intermediateOddKSNormWindow_radialSeriesSmall cfg j hj).2

end
end IsingBulk.HT.Tail
