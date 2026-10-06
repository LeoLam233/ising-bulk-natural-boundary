import IsingBulk.Tail.MicrocoreWindow
import IsingBulk.Tail.MicrocorePhaseMagnitude
import IsingBulk.Tail.MicrocoreKernel

/-! Source-attached nonwrapping Z geometry on all intermediate-window microcores. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Filter
open scoped BigOperators

 theorem original_microcore_window_geometry (d : LocalBranchData) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/4 ∧ ∀ A D : ℝ, 0 ≤ A → 0 ≤ D →
      ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ microcoreRadius A c N) →
      (∀ i, 0 < (originalPhase d (Real.exp (-H)) (u i)).re ∧
        (originalPhase d (Real.exp (-H)) (u i)).im < 0) ∧
      (∑ i, ‖originalPhase d (Real.exp (-H)) (u i)‖) ≤ 1/2 ∧
      (∑ i, ‖originalPhase d (Real.exp (-H)) (u i)‖)/4 ≤
        ‖1-IsingBulk.Jets.regularZProduct (radialParameter d.theta (Real.exp (-H)))
          (fun i => originalPhase d (Real.exp (-H)) (u i))‖ := by
  obtain ⟨cl,C,rP,_,hC,hrP,hP⟩ := original_phase_magnitude d
  obtain ⟨rB,hrB,hB⟩ := original_branch_inclusion d
  let c := min (min rP rB) (min (1/4) (1/(64*C^2)))/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcr : c < rP ∧ c < rB := by
    have hh : c < min (min rP rB) (min (1/4) (1/(64*C^2))) := half_lt_self (by positivity)
    exact ⟨hh.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
      hh.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hcb : c ≤ 1/4 ∧ c ≤ 1/(64*C^2) := by
    have hh : c ≤ min (min rP rB) (min (1/4) (1/(64*C^2))) := (half_le_self (by positivity))
    exact ⟨hh.trans ((min_le_right _ _).trans (min_le_left _ _)),
      hh.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hsmall : 2*C*Real.sqrt c ≤ 1/2 := by
    have hs := Real.sq_sqrt hc.le
    have hh := (le_div_iff₀ (by positivity : 0 < 64*C^2)).mp hcb.2
    have hp : 0 ≤ C*Real.sqrt c := by positivity
    nlinarith
  refine ⟨c,hc,hcb.1,?_⟩
  intro A D hA hD
  filter_upwards [microcore_window_epsilon_le_radius D A c hD hA hc] with H hH
  intro N hN hwindow u hu
  let b := microcoreRadius A c N
  have hb : 0 < b := microcoreRadius_pos A c hc N hN
  have hbc : b ≤ c := microcoreRadius_le_prefactor A c hA hc.le N hN
  have hεb : Real.exp (-H) ≤ b := hH N hN hwindow
  have hquad : ∀ i, 0 < (originalPhase d (Real.exp (-H)) (u i)).re ∧
      (originalPhase d (Real.exp (-H)) (u i)).im < 0 := by
    intro i
    obtain ⟨hre,him⟩ := hB _ _ (Real.exp_pos _) (hεb.trans_lt (hbc.trans_lt hcr.2))
      ((hu i).trans_lt (hbc.trans_lt hcr.2))
    have hh := lowerArccos_sheet _ hre him
    exact ⟨hh.2.1,hh.2.2.2⟩
  have hbound : ∀ i, ‖originalPhase d (Real.exp (-H)) (u i)‖ ≤ 2*C*Real.sqrt b := by
    intro i
    have hh := (hP _ _ (Real.exp_pos _) (hεb.trans_lt (hbc.trans_lt hcr.1))
      ((hu i).trans_lt (hbc.trans_lt hcr.1))).2
    have hs : Real.sqrt (|u i|+Real.exp (-H)) ≤ 2*Real.sqrt b := by
      have ht : |u i|+Real.exp (-H) ≤ 2*b := by linarith [hu i]
      have hs1 := Real.sq_sqrt (show 0 ≤ |u i|+Real.exp (-H) by positivity)
      have hs2 := Real.sq_sqrt hb.le
      nlinarith [Real.sqrt_nonneg (|u i|+Real.exp (-H)),Real.sqrt_nonneg b]
    exact hh.trans (by nlinarith)
  have hsum : (∑ i, ‖originalPhase d (Real.exp (-H)) (u i)‖) ≤ 1/2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    have hn := particle_sqrt_microcoreRadius_le A c hA hc N hN
    calc
      _ ≤ (N:ℝ)*(2*C*Real.sqrt b) := hh
      _ = 2*C*((N:ℝ)*Real.sqrt b) := by ring
      _ ≤ 2*C*Real.sqrt c := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ 1/2 := hsmall
  exact ⟨hquad,hsum,microcore_Z_gap _ _ (fun i => (hquad i).1.le)
    (fun i => (hquad i).2.le) hsum⟩

end
end IsingBulk.Tail
