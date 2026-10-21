import IsingBulk.HT.Tail.CompactRightWindow
import IsingBulk.HT.Tail.SignedCompactCurrentWindowBound
import IsingBulk.HT.Tail.SignedRightCompactNormBounds

/-! Full all-integer intermediate compact-right superseries for the signed
physical global kernel. The HT order and p+2 cutoff are literal; constants
are selected before the derivative order and no truncation is substituted. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set Filter Asymptotics
open scoped Topology

theorem signed_ht_original_compact_sector_window_littleO (ξ : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 : ℝ, 0 < alpha0 ∧ ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
      ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
      ∀ (p J : ℕ) (τ D : ℝ), 1 ≤ p → J ≤ (p^2-1)/2 → 0 ≤ τ → τ ≤ 1 → 0 ≤ D →
      radialSeriesSmall (fun eps N => htCompactRightWindow p D eps
        (fun N => signedOriginalRightCompactSectorNorm (Complex.exp (Complex.I*(ξ:ℂ))) N (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi J (radialParameter d.theta eps)) N) := by
  obtain ⟨eta0,he0,hmain⟩ := signed_original_compact_sector_window_bound ξ d hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,ha0,hmain⟩ := hmain eta he heL
  refine ⟨alpha0,ha0,?_⟩
  intro alpha ha haL outer inner ho hi his p J τ D hp hJ hτ hτ1 hD
  obtain ⟨S,hSn,hS,hmain⟩ := hmain alpha ha haL outer inner ho hi his J τ D hτ hτ1 hD
  apply htCompactRightWindow_small hp hJ D _
    (fun eps N => signedOriginalRightCompactSectorNorm_nonneg (Complex.exp (Complex.I*(ξ:ℂ))) N _ _ _ _ _ _ _ _ _ _)
    (fun N => mul_nonneg (zero_le_one.trans (compactSectorMultiplicity_one_le N)) (hSn N)) hS
  filter_upwards [hmain] with H hh
  intro n hND hdeg
  exact (signedOriginalRightCompactSectorNorm_le (Complex.exp (Complex.I*(ξ:ℂ))) _ _ _ _ _ _ ho hi J _ (mul_nonneg (hSn _) (sq_nonneg _))
    (hh n hND hdeg)).trans_eq (by ring)

theorem signed_ht_current_compact_sector_window_littleO (ξ : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 → tau ≤ 1 →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
        ∀ (p J : ℕ) (D β : ℝ), 1 ≤ p → J ≤ (p^2-1)/2 → 0 ≤ D → 0 < β →
        radialSeriesSmall (fun eps N => htCompactRightWindow p D eps
          (fun N => signedIntegratedRightCompactSectorNorm (Complex.exp (Complex.I*(ξ:ℂ))) N (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) tau d.thetaB outer inner ho hi J (radialParameter d.theta eps) (eps^β)) N) := by
  obtain ⟨eta0,he0,hmain⟩ := signed_current_compact_sector_window_bound ξ d hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hmain⟩ := hmain eta he heL
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL ht1 outer inner ho hi his p J D β hp hJ hD hβ
  obtain ⟨S,hSn,hS,hmain⟩ := hmain alpha tau ha haL ht htL ht1 outer inner ho hi his J D β hD hβ
  apply htCompactRightWindow_small hp hJ D _
    (fun eps N => signedIntegratedRightCompactSectorNorm_nonneg (Complex.exp (Complex.I*(ξ:ℂ))) N _ _ _ _ _ _ _ _ _ _ _)
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
  apply (signedIntegratedRightCompactSectorNorm_le (Complex.exp (Complex.I*(ξ:ℂ))) _ _ _ _ _ _ ho hi J _ (Q := S (n+1)*(H+1)^2)
    hcut (mul_nonneg (hSn _) (sq_nonneg _)) ?_).trans_eq (by ring)
  intro q qA sigma hσ lam hl
  exact hh n hND hdeg lam hl.1 (by simpa only [he] using hl.2) q qA sigma hσ


/-- Compact-right source closure with one selector choice for original and
small-current sectors and every permitted derivative order. -/
theorem signed_ht_compact_right_sector_sum_littleO (ξ : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
        ∀ (p J : ℕ) (D β : ℝ), 1 ≤ p → J ≤ (p^2-1)/2 → 0 ≤ D → 0 < β →
        radialSeriesSmall (fun eps N => htCompactRightWindow p D eps
          (fun N => signedRightCompactSectorNorm (Complex.exp (Complex.I*(ξ:ℂ))) N (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) tau d.thetaB outer inner ho hi J (radialParameter d.theta eps) (eps^β)) N) := by
  obtain ⟨etaO,heO,hO⟩ := signed_ht_original_compact_sector_window_littleO ξ d hcsmall
  obtain ⟨etaC,heC,hC⟩ := signed_ht_current_compact_sector_window_littleO ξ d hcsmall
  refine ⟨min etaO etaC,lt_min heO heC,?_⟩
  intro eta he heL
  obtain ⟨alphaO,haO,hO⟩ := hO eta he (heL.trans_le (min_le_left _ _))
  obtain ⟨alphaC,tauC,haC,htC,hC⟩ := hC eta he (heL.trans_le (min_le_right _ _))
  refine ⟨min alphaO alphaC,min tauC 1,lt_min haO haC,lt_min htC zero_lt_one,?_⟩
  intro alpha tau ha haL ht htL outer inner ho hi his p J D β hp hJ hD hβ
  have ht1 : tau ≤ 1 := htL.le.trans (min_le_right _ _)
  have hoSmall := hO alpha ha (haL.trans_le (min_le_left _ _)) outer inner ho hi his p J tau D hp hJ ht.le ht1 hD
  have hcSmall := hC alpha tau ha (haL.trans_le (min_le_right _ _)) ht
    (htL.trans_le (min_le_left _ _)) ht1 outer inner ho hi his p J D β hp hJ hD hβ
  simpa only [signedRightCompactSectorNorm,htCompactRightWindow_add] using hoSmall.add hcSmall

end
end IsingBulk.HT.Tail
