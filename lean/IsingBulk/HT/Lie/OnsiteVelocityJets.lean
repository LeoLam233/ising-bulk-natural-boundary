import IsingBulk.HT.Lie.OnsiteModel
import IsingBulk.Tail.MixedActiveVelocity
import IsingBulk.Tail.SectorAssignmentPartition

/-! Dimension-uniform finite jets of the actual onsite branch-only velocity.
There is no distinguished spectator and no selected-difference denominator. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem onsite_actual_velocity_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ c e t₀ C : ℝ,0< inner₀ ∧ inner₀≤cap ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧ 1≤C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      ∀ i,JetBound (onsiteActiveVelocity (mixedBranchIndexSet sigma) s
        (fun i => mixedContourPhase (constructedSelector d.thetaB η α)
          (Real.exp (-d.c₀*eps)) τ lam s θ i) i) 0 order C := by
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀≠0 := norm_ne_zero_iff.mp (by
    change ‖radialParameter d.theta 0‖≠0
    rw [radialParameter_norm (by norm_num)]
    norm_num)
  have hS : s₀+s₀⁻¹=1+(Real.cos d.thetaB:ℂ) := by
    simpa [IsingBulk.First.sourceS,s₀] using sourceS_radial_zero_branch d
  have hcos : |Real.cos d.thetaB|<1 := by
    have hsin : 0 < Real.sin d.thetaB := d.a_pos
    rw [abs_lt]
    constructor <;> nlinarith [hsin,Real.sin_sq_add_cos_sq d.thetaB,
      Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨inner₀,c,e,t₀,A,hi₀,hicap,hc,he,ht,hA,hjets⟩ :=
    mixed_actual_branch_function_jets d hcsmall regularA
      (regularA_analytic_base s₀ (Real.cos d.thetaB) hs₀ hS hcos) cap hcap order
  refine ⟨inner₀,c,e,t₀,max 1 A,hi₀,hicap,hc,he,ht,le_max_left _ _,?_⟩
  intro η α hη hηsmall hα inner hi hinner N eps τ lam θ sigma l s hN heps hepslt hτ hl0 hl1 htl hsupp hs i
  unfold onsiteActiveVelocity
  by_cases hiJ : i∈mixedBranchIndexSet sigma
  · have hσ : sigma i=2 := by simpa [mixedBranchIndexSet] using hiJ
    have hp := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp i
    rw [hσ] at hp
    have hj := hjets η α hη hηsmall hα N eps τ lam θ i s hN heps hepslt hτ hl0 hl1 htl
      ((sector_branch_label_profile hi hp).trans hinner) hs
    simpa only [hiJ,ite_true,mixedContourPhase] using
      hj.mono le_rfl (le_max_right 1 A)
  · simpa only [hiJ,ite_false] using
      (JetBound.const (0:ℂ) (0:MixedActiveSpace N) order).mono le_rfl
        (show ‖(0:ℂ)‖≤max 1 A by simp only [norm_zero]; exact zero_le_one.trans (le_max_left _ _))

end
end IsingBulk.HT.Lie
