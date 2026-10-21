import IsingBulk.HT.Tail.OddTailDomination
import IsingBulk.HT.Tail.CommonAllSectorParameters
import IsingBulk.Tail.IntermediateWindowAssembly

/-! The exact positive HT intermediate original/small-current norm window,
using one constructed selector, one current cutoff and the actual exhaustive
sector partition. The summation range begins at p+2 and the derivative ceiling
is supplied by the internally constructed HT common parameters. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set Filter Asymptotics
open scoped Topology

/-- The summand of the literal strict intermediate window. -/
def intermediateOddKSNormWindowTerm (p : ℕ) (d : LocalBranchData) (eta alpha tau : ℝ)
    (j : ℕ) (D eps cut : ℝ) (N : ℕ) : ℝ :=
  if p+2 ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps) then
    originalKSNorm N (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau j
      (radialParameter d.theta eps) cut else 0

theorem intermediateOddKSNormWindowTerm_nonneg (p : ℕ) (d : LocalBranchData)
    (eta alpha tau : ℝ) (j : ℕ) (D eps cut : ℝ) (N : ℕ) :
    0 ≤ intermediateOddKSNormWindowTerm p d eta alpha tau j D eps cut N := by
  unfold intermediateOddKSNormWindowTerm
  split_ifs
  · exact originalKSNorm_nonneg ..
  · exact le_rfl

theorem intermediateOddKSNormWindow_eq_tsum (p : ℕ) (d : LocalBranchData)
    (eta alpha tau : ℝ) (j : ℕ) (D eps cut : ℝ) :
    intermediateOddKSNormWindow p d eta alpha tau j D eps cut =
      ∑' N, intermediateOddKSNormWindowTerm p d eta alpha tau j D eps cut N := rfl

/-- A strict original window is contained in the weak window used by the
all-branch and compact-right estimates. No equality of the windows is used. -/
theorem ht_intermediate_window_subset {p N : ℕ} {D eps : ℝ}
    (hwindow : p+2 ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps)) :
    p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/eps)) := by
  constructor
  · omega
  · simpa only [one_div,Real.log_inv] using hwindow.2.le

/-- The mixed/left contribution is left unrestricted. The original
all-branch and compact-right contributions use their proved weak windows. -/
theorem intermediateOddKSNormWindowTerm_le_sector_windows (p : ℕ) (d : LocalBranchData)
    (eta outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (D : ℝ) (j : ℕ) (eps cut : ℝ)
    (hmajor : ∀ N : ℕ, p+2 ≤ N →
      originalKSNorm N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau j (radialParameter d.theta eps) cut ≤
      ‖iteratedDeriv j (originalSectorIntegral N (constructedSelector d.thetaB eta d.alpha)
        (Real.exp (-d.c₀*eps)) d.tau d.thetaB outer inner ho hi none)
          (radialParameter d.theta eps)‖ +
      mixedLeftSectorNorm N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau d.thetaB outer inner ho hi j (radialParameter d.theta eps) cut +
      rightCompactSectorNorm N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau d.thetaB outer inner ho hi j (radialParameter d.theta eps) cut)
    (N : ℕ) :
    intermediateOddKSNormWindowTerm p d eta d.alpha d.tau j D eps cut N ≤
      htOriginalAllBranchWindowTerm p d eta outer inner ho hi D j eps N +
      mixedLeftSectorNorm N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau d.thetaB outer inner ho hi j (radialParameter d.theta eps) cut +
      htCompactRightWindow p D eps
        (fun N => rightCompactSectorNorm N (constructedSelector d.thetaB eta d.alpha)
          (Real.exp (-d.c₀*eps)) d.tau d.thetaB outer inner ho hi j
            (radialParameter d.theta eps) cut) N := by
  by_cases hwindow : p+2 ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps)
  · have hwide := ht_intermediate_window_subset hwindow
    simpa only [intermediateOddKSNormWindowTerm,htOriginalAllBranchWindowTerm,htCompactRightWindow,
      ite_eq_left hwindow,ite_eq_left hwide] using hmajor N hwindow.1
  · rw [intermediateOddKSNormWindowTerm,ite_eq_right hwindow]
    exact add_nonneg
      (add_nonneg (htOriginalAllBranchWindowTerm_nonneg ..) (mixedLeftSectorNorm_nonneg ..))
      (htCompactRightWindow_nonneg p D eps (fun N => rightCompactSectorNorm_nonneg ..) N)

/-- The common sector choice controls the exact intermediate summands.
The comparison is obtained from the proved finite sector decomposition;
no norm domination or intermediate-window conclusion is assumed here. -/
theorem ht_common_intermediateOddKSNormWindow_radialSeriesSmall {p order : ℕ}
    {d : LocalBranchData} (cfg : HTCommonAllSectorParameters p d order)
    (j : ℕ) (hj : j ≤ order) :
    radialSeriesSmall (fun eps N => intermediateOddKSNormWindowTerm p d cfg.eta d.alpha d.tau
      j cfg.D eps (eps^cfg.beta) N) := by
  have hsectors := ((cfg.allBranch_small j hj).add (cfg.mixedLeft_small j hj)).add
    (cfg.rightCompact_small j hj)
  apply hsectors.of_eventually_le
  · intro eps N
    exact intermediateOddKSNormWindowTerm_nonneg ..
  · intro eps N
    exact add_nonneg
      (add_nonneg (htOriginalAllBranchWindowTerm_nonneg ..) (mixedLeftSectorNorm_nonneg ..))
      (htCompactRightWindow_nonneg p cfg.D eps
        (fun N => rightCompactSectorNorm_nonneg ..) N)
  · filter_upwards [radial_source_eventually_damping d cfg.c0_small,
      radial_power_cutoff_eventually cfg.beta_pos (0:ℝ) (show (0:ℝ) < 1 from zero_lt_one)]
      with eps hdomain hcut
    intro N
    apply intermediateOddKSNormWindowTerm_le_sector_windows p d cfg.eta cfg.outer cfg.inner
      cfg.outer_pos cfg.inner_pos cfg.D j eps (eps^cfg.beta) _ N
    intro M hM
    exact originalKSNorm_le_sectors M (by omega)
      (constructedSelector d.thetaB cfg.eta d.alpha) cfg.selector_regular
      hdomain.1 hdomain.2.1 d.tau_pos.le hcut.1 d.thetaB cfg.outer cfg.inner
      cfg.outer_pos cfg.inner_pos j (radialParameter d.theta eps) hdomain.2.2
      (fun q lam => cfg.current_allBranch_zero M q (Real.exp (-d.c₀*eps)) lam j
        (radialParameter d.theta eps))

/-- Little-o for the literal intermediate sum used by
`actual_higher_tail_domination`, retaining the common cutoff power. -/
theorem ht_common_intermediateOddKSNormWindow_littleO {p order : ℕ} {d : LocalBranchData}
    (cfg : HTCommonAllSectorParameters p d order) (j : ℕ) (hj : j ≤ order) :
    (fun eps : ℝ => intermediateOddKSNormWindow p d cfg.eta d.alpha d.tau j cfg.D eps
      (eps^cfg.beta)) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  exact (ht_common_intermediateOddKSNormWindow_radialSeriesSmall cfg j hj).2

end
end IsingBulk.HT.Tail
