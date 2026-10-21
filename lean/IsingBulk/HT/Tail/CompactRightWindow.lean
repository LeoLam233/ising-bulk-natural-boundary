import IsingBulk.HT.Lie.ExteriorWindow
import IsingBulk.Tail.CompactRightClosure

/-!
# Compact-right intermediate sectors at the HT order

The actual real-smooth coupled compact-sector estimates are already
all-dimensional. Their LT window wrappers use threshold 2*p+2 and order
(2*p)^2/2-1. This adapter uses p+2 and (p^2-1)/2 with the proved HT source
degree inequality. Densities, selector, Jacobian and cutoff support are
unchanged. The full intermediate all-integer superseries is controlled.
Only the positive-kernel sector is claimed here.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set Filter Asymptotics
open scoped Topology

def htCompactRightWindow (p : ℕ) (D eps : ℝ) (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  if p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/eps)) then F N else 0

theorem htCompactRightWindow_nonneg (p : ℕ) (D eps : ℝ) {F : ℕ → ℝ} (hF : ∀ N, 0 ≤ F N) (N : ℕ) :
    0 ≤ htCompactRightWindow p D eps F N := by
  unfold htCompactRightWindow
  split_ifs
  · exact hF N
  · exact le_rfl

theorem htCompactRightWindow_small {p J : ℕ} (hp : 1 ≤ p) (hJ : J ≤ (p^2-1)/2)
    (D : ℝ) (E : ℝ → ℕ → ℝ) (hE : ∀ eps N, 0 ≤ E eps N)
    {S : ℕ → ℝ} (hSn : ∀ N, 0 ≤ S N) (hS : Summable S)
    (hb : ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H → 2*J+1 ≤ (n+1)*n →
      E (Real.exp (-H)) (n+1) ≤ S (n+1)*(H+1)^2) :
    radialSeriesSmall (fun eps N => htCompactRightWindow p D eps (E eps) N) := by
  apply radialSeriesSmall_of_log_majorant _ (fun eps N => htCompactRightWindow_nonneg p D eps (hE eps) N) hS
  filter_upwards [log_inverse_tendsto_atTop.eventually hb,self_mem_nhdsWithin] with eps hH heps
  intro N
  unfold htCompactRightWindow
  split_ifs with hwindow
  · have hdeg := IsingBulk.HT.Lie.exterior_source_degree hp hwindow.1 hJ
    have hN : 1 ≤ N := by omega
    have hn : N-1+1=N := Nat.sub_add_cancel hN
    have he : Real.exp (-Real.log (1/eps))=eps := by rw [one_div,Real.log_inv,neg_neg,Real.exp_log heps]
    have hh := hH (N-1) (by rw [hn]; exact hwindow.2) (by rw [hn]; omega)
    simpa only [hn,he] using hh
  · exact mul_nonneg (hSn N) (sq_nonneg _)

theorem ht_original_compact_sector_window_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 : ℝ, 0 < alpha0 ∧ ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
      ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
      ∀ (p J : ℕ) (τ D : ℝ), 1 ≤ p → J ≤ (p^2-1)/2 → 0 ≤ τ → τ ≤ 1 → 0 ≤ D →
      radialSeriesSmall (fun eps N => htCompactRightWindow p D eps
        (fun N => originalRightCompactSectorNorm N (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi J (radialParameter d.theta eps)) N) := by
  obtain ⟨eta0,he0,hmain⟩ := original_compact_sector_window_bound d hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,ha0,hmain⟩ := hmain eta he heL
  refine ⟨alpha0,ha0,?_⟩
  intro alpha ha haL outer inner ho hi his p J τ D hp hJ hτ hτ1 hD
  obtain ⟨S,hSn,hS,hmain⟩ := hmain alpha ha haL outer inner ho hi his J τ D hτ hτ1 hD
  apply htCompactRightWindow_small hp hJ D _
    (fun eps N => originalRightCompactSectorNorm_nonneg N _ _ _ _ _ _ _ _ _ _)
    (fun N => mul_nonneg (zero_le_one.trans (compactSectorMultiplicity_one_le N)) (hSn N)) hS
  filter_upwards [hmain] with H hh
  intro n hND hdeg
  exact (originalRightCompactSectorNorm_le _ _ _ _ _ _ ho hi J _ (mul_nonneg (hSn _) (sq_nonneg _))
    (hh n hND hdeg)).trans_eq (by ring)

theorem ht_current_compact_sector_window_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 → tau ≤ 1 →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
        ∀ (p J : ℕ) (D β : ℝ), 1 ≤ p → J ≤ (p^2-1)/2 → 0 ≤ D → 0 < β →
        radialSeriesSmall (fun eps N => htCompactRightWindow p D eps
          (fun N => integratedRightCompactSectorNorm N (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) tau d.thetaB outer inner ho hi J (radialParameter d.theta eps) (eps^β)) N) := by
  obtain ⟨eta0,he0,hmain⟩ := current_compact_sector_window_bound d hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hmain⟩ := hmain eta he heL
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL ht1 outer inner ho hi his p J D β hp hJ hD hβ
  obtain ⟨S,hSn,hS,hmain⟩ := hmain alpha tau ha haL ht htL ht1 outer inner ho hi his J D β hD hβ
  apply htCompactRightWindow_small hp hJ D _
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


theorem htCompactRightWindow_add (p : ℕ) (D eps : ℝ) (F G : ℕ → ℝ) (N : ℕ) :
    htCompactRightWindow p D eps (fun N => F N+G N) N=
      htCompactRightWindow p D eps F N+htCompactRightWindow p D eps G N := by
  unfold htCompactRightWindow
  split_ifs <;> simp

/-- Compact-right source closure with one selector choice for original and
small-current sectors and every permitted derivative order. -/
theorem ht_compact_right_sector_sum_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
        ∀ (p J : ℕ) (D β : ℝ), 1 ≤ p → J ≤ (p^2-1)/2 → 0 ≤ D → 0 < β →
        radialSeriesSmall (fun eps N => htCompactRightWindow p D eps
          (fun N => rightCompactSectorNorm N (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) tau d.thetaB outer inner ho hi J (radialParameter d.theta eps) (eps^β)) N) := by
  obtain ⟨etaO,heO,hO⟩ := ht_original_compact_sector_window_littleO d hcsmall
  obtain ⟨etaC,heC,hC⟩ := ht_current_compact_sector_window_littleO d hcsmall
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
  simpa only [rightCompactSectorNorm,htCompactRightWindow_add] using hoSmall.add hcSmall

end
end IsingBulk.HT.Tail
