import IsingBulk.HT22.Anchor.IntegralIdentity
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The completed true anchor estimate for the original physical signed
coefficients: all complex derivative orders, all odd N≥3, all named cells.
No generated-density, contour, derivative-exchange, or endpoint bound remains
as a hypothesis. The regime precedes every particle and derivative order. -/
theorem actual_anchor_derivative_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ r : ℝ → ℝ,PreferredRightCutoffData d B δB r →
      ∀ J : ℕ,∃ C : ℝ,0<C ∧
      ∀ negative : Bool,∀ n : ℕ,0<n → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ a : Fin (2*n+1),∀ j≤J,
      ‖iteratedDeriv j (Physical.anchorPopulationIntegral negative (2*n) a τ preferredPopulationCutoff B.p B.m r)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤
        (C/Real.sqrt (2*n+1:ℕ))^(2*n+1)*(2*n+1:ℕ)^(J*J+8*J+1) := by
  obtain ⟨cap,hcap,hcapa,hbound⟩ := actual_anchor_integrated_bound d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨εb,τb,hεb,hτb,hb⟩ := hbound B hB δB hδB
  obtain ⟨τi,εi,hτi,hεi,hi⟩ := actual_anchor_integral_identity d B
  refine ⟨min εb εi,min τb τi,lt_min hεb hεi,lt_min hτb hτi,?_⟩
  intro r hcut J
  obtain ⟨C,hC,hj⟩ := hb r hcut J
  refine ⟨C,hC,?_⟩
  intro negative n hn ε τ hε hεr hτ hτr a j hjJ
  rw [hi τ hτ (hτr.trans_le (min_le_right _ _)) r hcut.2.2.1 hcut.2.2.2.1
    negative n a j ε hε (hεr.trans_le (min_le_right _ _))]
  exact hj negative (2*n) (by omega) ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) a j hjJ
end
end IsingBulk.HT22.Anchor
