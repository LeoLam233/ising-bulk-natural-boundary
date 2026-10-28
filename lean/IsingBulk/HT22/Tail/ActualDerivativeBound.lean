import IsingBulk.HT22.Tail.ActualIntegralIdentity

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

theorem actual_right_derivative_bound (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d, B.delta<cap →
    ∃ ε₀ τ₀ δ₀ : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ H A : ℝ, ∃ L : ℕ, 0<H ∧ 0<A ∧
    ∀ δ : ℝ, δ≤δ₀ → PreferredRightCutoffData d B δ rcut →
    ∀ n : ℕ, 2*j+9≤(2*n+3)^2 → ∀ negative : Bool, ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ‖iteratedDeriv j (Physical.rightPopulationIntegral negative (2*n+2) τ
        preferredPopulationCutoff B.p B.m rcut) (IsingBulk.Branch.radialParameter d.alpha ε)‖≤
      (H*nearOrderEnvelope (2*n+3)+farOrderEnvelope A L (2*n+3))*(1+|Real.log ε|) := by
  obtain ⟨ci,hci,hcia,hi⟩ := actual_right_integral_identity d
  obtain ⟨cw,hcw,_,hw⟩ := Far.actual_whole_angular_mass d
  refine ⟨min ci cw,lt_min hci hcw,lt_of_le_of_lt (min_le_left _ _) hcia,?_⟩
  intro B hB
  obtain ⟨ei,ti,di,hei,hti,hdi,hdiB,hi⟩ := hi B (lt_of_lt_of_le hB (min_le_left _ _))
  obtain ⟨ew,tw,dw,hew,htw,hdw,_,hw⟩ := hw B (lt_of_lt_of_le hB (min_le_right _ _))
  refine ⟨min ei ew,min ti tw,min di dw,lt_min hei hew,lt_min hti htw,lt_min hdi hdw,
    lt_of_le_of_lt (min_le_left _ _) hdiB,?_⟩
  intro rcut hr hp j
  obtain ⟨H,A,L,hH,hA,hw⟩ := hw rcut hr hp j
  refine ⟨H,A,L,hH,hA,?_⟩
  intro δ hδ hcut n hdeg negative ε τ hε hεr hτ hτr
  rw [hi δ (le_trans hδ (min_le_left _ _)) rcut hcut j n hdeg negative τ hτ
    (lt_of_lt_of_le hτr (min_le_left _ _)) j le_rfl ε hε
    (lt_of_lt_of_le hεr (min_le_left _ _))]
  have hb := hw (Physical.constraintAngle negative) (Physical.constraintAngle negative)
    (constraintAngle_abs_le_pi negative) n (by omega) ε τ hε
    (lt_of_lt_of_le hεr (min_le_right _ _)) hτ (lt_of_lt_of_le hτr (min_le_right _ _)) δ
    (le_trans hδ (min_le_right _ _)) hcut
  have hR : 0≤(H*nearOrderEnvelope (2*n+3)+farOrderEnvelope A L (2*n+3))*(1+|Real.log ε|) := by
    apply mul_nonneg _ (by positivity)
    exact completeOrderEnvelope_nonneg hH.le hA.le L (2*n+3)
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hR] at hb'
  have hv := (norm_integral_le_lintegral_norm _).trans hb'
  simpa only [transportedIntegral,Physical.constrainedAngles,constrainedAtTotal,
    constraintSign_eq_signed_exp] using hv

end
end IsingBulk.HT22.Tail
