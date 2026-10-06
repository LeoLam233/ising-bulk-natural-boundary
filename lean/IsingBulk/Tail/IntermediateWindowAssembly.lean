import IsingBulk.Tail.AllOrderTailDomination
import IsingBulk.Tail.AllBranchSectorAsymptotic
import IsingBulk.Tail.CompactRightClosure
import IsingBulk.Tail.CommonAllSectorParameters
import IsingBulk.Tail.ExactSectorNormDomination

/-! Transfer of the three actual intermediate-sector estimates to the
strict particle window occurring in the absolute-tail comparison. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Asymptotics
open scoped Topology

/-- Nonnegative termwise domination preserves both parts of radial series
smallness: eventual summability and little-o of the actual infinite sum. -/
theorem radialSeriesSmall.of_eventually_le {E F : ℝ → ℕ → ℝ}
    (hF : radialSeriesSmall F) (hEn : ∀ eps N, 0 ≤ E eps N)
    (hFn : ∀ eps N, 0 ≤ F eps N)
    (hEF : ∀ᶠ eps : ℝ in 𝓝[>] 0, ∀ N, E eps N ≤ F eps N) :
    radialSeriesSmall E := by
  have hsum : ∀ᶠ eps : ℝ in 𝓝[>] 0, Summable (E eps) := by
    filter_upwards [hF.1,hEF] with eps hs hle
    exact Summable.of_nonneg_of_le (hEn eps) hle hs
  refine ⟨hsum,?_⟩
  have hO : (fun eps : ℝ => ∑' N, E eps N) =O[𝓝[>] 0]
      (fun eps : ℝ => ∑' N, F eps N) := by
    apply IsBigO.of_bound 1
    filter_upwards [hsum,hF.1,hEF] with eps hsE hsF hle
    have hh := Summable.tsum_le_tsum hle hsE hsF
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hEn eps)),
      abs_of_nonneg (tsum_nonneg (hFn eps)),one_mul] using hh
  exact hO.trans_isLittleO hF.2

/-- The summand of the literal strict intermediate window. -/
def intermediateKSNormWindowTerm (p : ℕ) (d : LocalBranchData) (eta alpha tau : ℝ)
    (j : ℕ) (D eps cut : ℝ) (N : ℕ) : ℝ :=
  if 2*(p+1) ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps) then
    originalKSNorm N (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau j
      (radialParameter d.theta eps) cut else 0

theorem intermediateKSNormWindowTerm_nonneg (p : ℕ) (d : LocalBranchData)
    (eta alpha tau : ℝ) (j : ℕ) (D eps cut : ℝ) (N : ℕ) :
    0 ≤ intermediateKSNormWindowTerm p d eta alpha tau j D eps cut N := by
  unfold intermediateKSNormWindowTerm
  split_ifs
  · exact originalKSNorm_nonneg ..
  · exact le_rfl

theorem intermediateKSNormWindow_eq_tsum (p : ℕ) (d : LocalBranchData)
    (eta alpha tau : ℝ) (j : ℕ) (D eps cut : ℝ) :
    intermediateKSNormWindow p d eta alpha tau j D eps cut =
      ∑' N, intermediateKSNormWindowTerm p d eta alpha tau j D eps cut N := rfl

/-- A strict original window is contained in the weak window used by the
all-branch and compact-right estimates. No equality of the windows is used. -/
theorem intermediate_window_subset {p N : ℕ} {D eps : ℝ}
    (hwindow : 2*(p+1) ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps)) :
    2*p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/eps)) := by
  constructor
  · omega
  · simpa only [one_div,Real.log_inv] using hwindow.2.le

/-- The mixed/left contribution is left unrestricted. The original
all-branch and compact-right contributions use their proved weak windows. -/
theorem intermediateKSNormWindowTerm_le_sector_windows (p : ℕ) (d : LocalBranchData)
    (eta outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (D : ℝ) (j : ℕ) (eps cut : ℝ)
    (hmajor : ∀ N : ℕ, 2*(p+1) ≤ N →
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
    intermediateKSNormWindowTerm p d eta d.alpha d.tau j D eps cut N ≤
      originalAllBranchWindowTerm p d eta outer inner ho hi D j eps N +
      mixedLeftSectorNorm N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
        d.tau d.thetaB outer inner ho hi j (radialParameter d.theta eps) cut +
      compactRightWindow p D eps
        (fun N => rightCompactSectorNorm N (constructedSelector d.thetaB eta d.alpha)
          (Real.exp (-d.c₀*eps)) d.tau d.thetaB outer inner ho hi j
            (radialParameter d.theta eps) cut) N := by
  by_cases hwindow : 2*(p+1) ≤ N ∧ (N:ℝ) < D*Real.sqrt (-Real.log eps)
  · have hwide := intermediate_window_subset hwindow
    simpa only [intermediateKSNormWindowTerm,originalAllBranchWindowTerm,compactRightWindow,
      ite_eq_left hwindow,ite_eq_left hwide] using hmajor N hwindow.1
  · rw [intermediateKSNormWindowTerm,ite_eq_right hwindow]
    exact add_nonneg
      (add_nonneg (originalAllBranchWindowTerm_nonneg ..) (mixedLeftSectorNorm_nonneg ..))
      (compactRightWindow_nonneg p D eps (fun N => rightCompactSectorNorm_nonneg ..) N)

/-- The common sector choice controls the exact intermediate summands.
The comparison is obtained from the proved finite sector decomposition;
no norm domination or intermediate-window conclusion is assumed here. -/
theorem common_intermediateKSNormWindow_radialSeriesSmall {p order : ℕ}
    {d : LocalBranchData} (cfg : CommonAllSectorParameters p d order)
    (j : ℕ) (hj : j ≤ order) :
    radialSeriesSmall (fun eps N => intermediateKSNormWindowTerm p d cfg.eta d.alpha d.tau
      j cfg.D eps (eps^cfg.beta) N) := by
  have hsectors := ((cfg.allBranch_small j hj).add (cfg.mixedLeft_small j hj)).add
    (cfg.rightCompact_small j hj)
  apply hsectors.of_eventually_le
  · intro eps N
    exact intermediateKSNormWindowTerm_nonneg ..
  · intro eps N
    exact add_nonneg
      (add_nonneg (originalAllBranchWindowTerm_nonneg ..) (mixedLeftSectorNorm_nonneg ..))
      (compactRightWindow_nonneg p cfg.D eps
        (fun N => rightCompactSectorNorm_nonneg ..) N)
  · filter_upwards [radial_source_eventually_damping d cfg.c0_small,
      radial_power_cutoff_eventually cfg.beta_pos (0:ℝ) (show (0:ℝ) < 1 from zero_lt_one)]
      with eps hdomain hcut
    intro N
    apply intermediateKSNormWindowTerm_le_sector_windows p d cfg.eta cfg.outer cfg.inner
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
theorem common_intermediateKSNormWindow_littleO {p order : ℕ} {d : LocalBranchData}
    (cfg : CommonAllSectorParameters p d order) (j : ℕ) (hj : j ≤ order) :
    (fun eps : ℝ => intermediateKSNormWindow p d cfg.eta d.alpha d.tau j cfg.D eps
      (eps^cfg.beta)) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  exact (common_intermediateKSNormWindow_radialSeriesSmall cfg j hj).2

end
end IsingBulk.Tail
