import IsingBulk.Tail.CompactCurrentWindowBound
import IsingBulk.Tail.RightCompactSectorNorm
import IsingBulk.Tail.MixedLeftAsymptotic
import IsingBulk.Tail.AllBranchExteriorAsymptotic

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Asymptotics
open scoped Topology
set_option maxHeartbeats 1800000

def compactRightWindow (p : ℕ) (D eps : ℝ) (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  if 2*p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/eps)) then F N else 0

theorem compactRightWindow_nonneg (p : ℕ) (D eps : ℝ) {F : ℕ → ℝ} (hF : ∀ N, 0 ≤ F N) (N : ℕ) :
    0 ≤ compactRightWindow p D eps F N := by
  unfold compactRightWindow
  split_ifs
  · exact hF N
  · exact le_rfl

theorem radialSeriesSmall_of_log_majorant (E : ℝ → ℕ → ℝ) (hE : ∀ eps N, 0 ≤ E eps N)
    {S : ℕ → ℝ} (hS : Summable S)
    (hbound : ∀ᶠ eps : ℝ in 𝓝[>] 0, ∀ N, E eps N ≤ S N*(Real.log (1/eps)+1)^2) :
    radialSeriesSmall E := by
  have hsum : ∀ᶠ eps : ℝ in 𝓝[>] 0, Summable (E eps) := by
    filter_upwards [hbound] with eps hb
    exact Summable.of_nonneg_of_le (hE eps) hb (hS.mul_right _)
  refine ⟨hsum,?_⟩
  have hO : (fun eps : ℝ => ∑' N, E eps N) =O[𝓝[>] 0] (fun eps : ℝ => (Real.log (1/eps)+1)^2) := by
    apply IsBigO.of_bound (∑' N, S N)
    filter_upwards [hbound,hsum] with eps hb hs
    have hh := Summable.tsum_le_tsum hb hs (hS.mul_right _)
    rw [tsum_mul_right] at hh
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hE eps)),
      abs_of_nonneg (sq_nonneg (Real.log (1/eps)+1))] using hh
  exact hO.trans_isLittleO radial_log_polynomial_littleO

theorem compactRightWindow_small {p J : ℕ} (hp : 1 ≤ p) (hJ : J ≤ (2*p)^2/2-1)
    (D : ℝ) (E : ℝ → ℕ → ℝ) (hE : ∀ eps N, 0 ≤ E eps N)
    {S : ℕ → ℝ} (hSn : ∀ N, 0 ≤ S N) (hS : Summable S)
    (hb : ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H → 2*J+1 ≤ (n+1)*n →
      E (Real.exp (-H)) (n+1) ≤ S (n+1)*(H+1)^2) :
    radialSeriesSmall (fun eps N => compactRightWindow p D eps (E eps) N) := by
  apply radialSeriesSmall_of_log_majorant _ (fun eps N => compactRightWindow_nonneg p D eps (hE eps) N) hS
  filter_upwards [log_inverse_tendsto_atTop.eventually hb,self_mem_nhdsWithin] with eps hH heps
  intro N
  unfold compactRightWindow
  split_ifs with hwindow
  · have hdeg := allBranchExterior_source_degree hp hwindow.1 hJ
    have hN : 1 ≤ N := by omega
    have hn : N-1+1=N := Nat.sub_add_cancel hN
    have he : Real.exp (-Real.log (1/eps))=eps := by rw [one_div,Real.log_inv,neg_neg,Real.exp_log heps]
    have hh := hH (N-1) (by rw [hn]; exact hwindow.2) (by rw [hn]; omega)
    simpa only [hn,he] using hh
  · exact mul_nonneg (hSn N) (sq_nonneg _)

theorem original_compact_sector_window_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 : ℝ, 0 < alpha0 ∧ ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
      ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
      ∀ (p J : ℕ) (τ D : ℝ), 1 ≤ p → J ≤ (2*p)^2/2-1 → 0 ≤ τ → τ ≤ 1 → 0 ≤ D →
      radialSeriesSmall (fun eps N => compactRightWindow p D eps
        (fun N => originalRightCompactSectorNorm N (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi J (radialParameter d.theta eps)) N) := by
  obtain ⟨eta0,he0,hmain⟩ := original_compact_sector_window_bound d hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,ha0,hmain⟩ := hmain eta he heL
  refine ⟨alpha0,ha0,?_⟩
  intro alpha ha haL outer inner ho hi his p J τ D hp hJ hτ hτ1 hD
  obtain ⟨S,hSn,hS,hmain⟩ := hmain alpha ha haL outer inner ho hi his J τ D hτ hτ1 hD
  apply compactRightWindow_small hp hJ D _
    (fun eps N => originalRightCompactSectorNorm_nonneg N _ _ _ _ _ _ _ _ _ _)
    (fun N => mul_nonneg (zero_le_one.trans (compactSectorMultiplicity_one_le N)) (hSn N)) hS
  filter_upwards [hmain] with H hh
  intro n hND hdeg
  exact (originalRightCompactSectorNorm_le _ _ _ _ _ _ ho hi J _ (mul_nonneg (hSn _) (sq_nonneg _))
    (hh n hND hdeg)).trans_eq (by ring)

theorem current_compact_sector_window_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 → tau ≤ 1 →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
        ∀ (p J : ℕ) (D β : ℝ), 1 ≤ p → J ≤ (2*p)^2/2-1 → 0 ≤ D → 0 < β →
        radialSeriesSmall (fun eps N => compactRightWindow p D eps
          (fun N => integratedRightCompactSectorNorm N (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) tau d.thetaB outer inner ho hi J (radialParameter d.theta eps) (eps^β)) N) := by
  obtain ⟨eta0,he0,hmain⟩ := current_compact_sector_window_bound d hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hmain⟩ := hmain eta he heL
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL ht1 outer inner ho hi his p J D β hp hJ hD hβ
  obtain ⟨S,hSn,hS,hmain⟩ := hmain alpha tau ha haL ht htL ht1 outer inner ho hi his J D β hD hβ
  apply compactRightWindow_small hp hJ D _
    (fun eps N => integratedRightCompactSectorNorm_nonneg N _ _ _ _ _ _ _ _ _ _ _)
    (fun N => mul_nonneg (zero_le_one.trans (compactSectorMultiplicity_one_le N)) (hSn N)) hS
  filter_upwards [hmain,eventually_ge_atTop (0:ℝ)] with H hh hH
  intro n hND hdeg
  have he : (Real.exp (-H))^β=Real.exp (-β*H) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  have hcut : (Real.exp (-H))^β ∈ Icc (0:ℝ) 1 := by
    rw [he]
    exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by nlinarith)⟩
  apply (integratedRightCompactSectorNorm_le _ _ _ _ _ _ ho hi J _ (Q := S (n+1)*(H+1)^2)
    hcut (mul_nonneg (hSn _) (sq_nonneg _)) ?_).trans_eq (by ring)
  intro q qA sigma hσ lam hl
  exact hh n hND hdeg lam hl.1 (by simpa only [he] using hl.2) q qA sigma hσ

end
end IsingBulk.Tail
