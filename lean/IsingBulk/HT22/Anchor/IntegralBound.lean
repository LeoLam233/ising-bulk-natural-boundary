import IsingBulk.HT22.Anchor.SignedProfileMass
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete signed, lifted physical anchor descendant integral. -/
def transportedIntegral (negative : Bool) (n : ℕ) (a : Fin (n+1))
    (δ τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) (t : ℂ) : ℂ :=
  ∫ θ in angularBox n,transportedDensity a (Physical.constraintSign negative) τ η p m r j t
    (preferredLiftedAngles δ (Physical.constrainedAngles negative n θ))

/-- Actual integrated all-order anchor bound, including the separately
controlled three-particle term. This estimates the literal descendants;
identification with derivatives of the original integral is kept separate. -/
theorem actual_anchor_integrated_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ J : ℕ,∃ C : ℝ,0<C ∧
      ∀ negative : Bool,∀ n : ℕ,3≤n+1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ a : Fin (n+1),∀ j≤J,
      ‖transportedIntegral negative n a B.delta τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤
        (C/Real.sqrt (n+1:ℕ))^(n+1)*(n+1:ℕ)^(J*J+8*J+1) := by
  obtain ⟨cap,hcap,hcapa,hpoint⟩ := actual_anchor_pointwise_bound d
  obtain ⟨D,hD,hmass⟩ := signed_anchor_profile_mass d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨ε₀,τ₀,hε₀,hτ₀,hbound⟩ := hpoint B hB δB hδB
  refine ⟨min ε₀ 1,τ₀,lt_min hε₀ zero_lt_one,hτ₀,?_⟩
  intro rcut hcut J
  obtain ⟨C,hC,hb⟩ := hbound rcut hcut J
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro negative n hn ε τ hε hεr hτ hτr a j hj
  let A := (C/Real.sqrt (n+1:ℕ))^(n+1)*(n+1:ℕ)^(J*J+8*J+1)
  have hA : 0≤A := by dsimp [A]; positivity
  have hsign : ‖Physical.constraintSign negative‖=1 := by cases negative <;> simp [Physical.constraintSign]
  have hdom : ∀ θ : Fin n → ℝ,
      ‖transportedDensity a (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε)
        (preferredLiftedAngles B.delta (Physical.constrainedAngles negative n θ))‖≤
      A*preferredAnchorProfile d ε a (Physical.constrainedAngles negative n θ) := by
    intro θ
    exact hb (n+1) (by omega) _ hsign ε τ hε (hεr.trans_le (min_le_left _ _)) hτ hτr _ a j hj
  have hi := (signed_anchor_profile_integrable d negative n hε a).const_mul A
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hdom)
  change ‖transportedIntegral negative n a B.delta τ preferredPopulationCutoff B.p B.m rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε)‖≤_ at hh
  rw [integral_const_mul] at hh
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (hmass negative n hn ε hε
    (hεr.le.trans (min_le_right _ _)) a) hA
  apply hm.trans_eq
  dsimp [A]
  simp only [mul_pow,div_pow]
  ring
end
end IsingBulk.HT22.Anchor
