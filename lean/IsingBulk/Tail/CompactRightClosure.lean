import IsingBulk.Tail.CompactWindowAsymptotic

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Asymptotics
open scoped Topology

def rightCompactSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) (s : ℂ) (cut : ℝ) : ℝ :=
  originalRightCompactSectorNorm N f r τ b outer inner ho hi J s+
    integratedRightCompactSectorNorm N f r τ b outer inner ho hi J s cut

theorem rightCompactSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ rightCompactSectorNorm N f r τ b outer inner ho hi J s cut :=
  add_nonneg (originalRightCompactSectorNorm_nonneg ..) (integratedRightCompactSectorNorm_nonneg ..)

theorem compactRightWindow_add (p : ℕ) (D eps : ℝ) (F G : ℕ → ℝ) (N : ℕ) :
    compactRightWindow p D eps (fun N => F N+G N) N=
      compactRightWindow p D eps F N+compactRightWindow p D eps G N := by
  unfold compactRightWindow
  split_ifs <;> simp

/-- Compact-right source closure with one selector choice for original and
small-current sectors and every permitted derivative order. -/
theorem compact_right_sector_sum_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
        ∀ (p J : ℕ) (D β : ℝ), 1 ≤ p → J ≤ (2*p)^2/2-1 → 0 ≤ D → 0 < β →
        radialSeriesSmall (fun eps N => compactRightWindow p D eps
          (fun N => rightCompactSectorNorm N (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) tau d.thetaB outer inner ho hi J (radialParameter d.theta eps) (eps^β)) N) := by
  obtain ⟨etaO,heO,hO⟩ := original_compact_sector_window_littleO d hcsmall
  obtain ⟨etaC,heC,hC⟩ := current_compact_sector_window_littleO d hcsmall
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
  simpa only [rightCompactSectorNorm,compactRightWindow_add] using hoSmall.add hcSmall

end
end IsingBulk.Tail
