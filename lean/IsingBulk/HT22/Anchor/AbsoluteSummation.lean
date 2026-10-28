import IsingBulk.HT22.Anchor.DerivativeBound
import IsingBulk.Preferred22.AbsoluteTail
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All named anchors at the actual odd order N=2(k+1)+1≥3. -/
def derivativeMass (negative : Bool) (k : ℕ) (τ : ℝ) (p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) : ℝ :=
  ∑ a : Fin (2*(k+1)+1),‖iteratedDeriv j
    (Physical.anchorPopulationIntegral negative (2*(k+1)) a τ preferredPopulationCutoff p m r) s‖

def oddAnchorEnvelope (C : ℝ) (J k : ℕ) : ℝ :=
  shellOrderEnvelope C (J*J+8*J+2) (2*(k+1)+1)

theorem derivativeMass_nonneg (negative : Bool) (k : ℕ) (τ : ℝ) (p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) : 0≤derivativeMass negative k τ p m r j s :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem oddAnchorEnvelope_summable {C : ℝ} (hC : 0≤C) (J : ℕ) :
    Summable (oddAnchorEnvelope C J) :=
  (shell_order_envelope_summable hC (J*J+8*J+2)).comp_injective (fun _ _ h => by omega)

/-- Uniform all-particle absolute majorant, with the additional N anchors
counted explicitly. The original physical coefficients appear in derivativeMass. -/
theorem actual_anchor_absolute_majorant (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ r : ℝ → ℝ,PreferredRightCutoffData d B δB r →
      ∀ J : ℕ,∃ C : ℝ,0<C ∧ Summable (oddAnchorEnvelope C J) ∧
      ∀ negative : Bool,∀ k : ℕ,∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ j≤J,
      derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)≤
        oddAnchorEnvelope C J k := by
  obtain ⟨cap,hcap,hcapa,hbound⟩ := actual_anchor_derivative_bound d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨ε₀,τ₀,hε₀,hτ₀,hb⟩ := hbound B hB δB hδB
  refine ⟨ε₀,τ₀,hε₀,hτ₀,?_⟩
  intro r hcut J
  obtain ⟨C,hC,hj⟩ := hb r hcut J
  refine ⟨C,hC,oddAnchorEnvelope_summable hC.le J,?_⟩
  intro negative k ε τ hε hεr hτ hτr j hjJ
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (2*(k+1)+1))))
    (fun a _ => hj negative (k+1) (by omega) ε τ hε hεr hτ hτr a j hjJ)
  change derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)≤_ at hh
  apply hh.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold oddAnchorEnvelope shellOrderEnvelope
  rw [show J*J+8*J+2=(J*J+8*J+1)+1 by omega,pow_succ]
  ring

/-- Absolute summability of all actual anchor derivatives follows from the
explicit numerical majorant, not from per-N contour summability. -/
theorem derivativeMass_summable_of_bound (negative : Bool) (τ : ℝ) (p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) {C : ℝ} (hC : 0≤C) (J : ℕ)
    (hbound : ∀ k,derivativeMass negative k τ p m r j s≤oddAnchorEnvelope C J k) :
    Summable (fun k => derivativeMass negative k τ p m r j s) :=
  (oddAnchorEnvelope_summable hC J).of_nonneg_of_le
    (fun k => derivativeMass_nonneg negative k τ p m r j s) hbound
end
end IsingBulk.HT22.Anchor
