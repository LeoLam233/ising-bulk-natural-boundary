import IsingBulk.Preferred22.LowerInnerIntegral
import IsingBulk.Preferred22.WeightedRightPartition

/-! The complete physical right integral at every lower positive even
order has the all-order logarithmic derivative bound. The original equality
tube and its complementary weighted transported integral are both included. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_lower_right_derivative_log (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∀ n : ℕ,2≤n+1 → Even (n+1) → n+1<2*p →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ j : ℕ,∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (preferredTransportedIntegral (n := n) .right B.delta τ
          preferredPopulationCutoff B.p B.m rcut 0)
            (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,houter⟩ := preferred_actual_outer_right_derivative_log d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB n hN hEven hNp
  obtain ⟨δo,τo,εo,hδo,hδoB,hτo,hεo,ho⟩ := houter B hB
  obtain ⟨δi,Ri,τi,εi,hδi,hRi,hτi,hεi,hi⟩ :=
    preferred_actual_lower_inner_derivative_bound d hp hp5 ha hα n hEven hNp B
  refine ⟨min δo δi,min τo τi,min εo εi,lt_min hδo hδi,
    (min_le_left _ _).trans_lt hδoB,lt_min hτo hτi,lt_min hεo hεi,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr j
  obtain ⟨A,hA,ho'⟩ := ho δB hδB (hδB₀.trans (min_le_left _ _)) rcut hcut τ hτ
    (hτr.trans_le (min_le_left _ _)) n hN hEven Ri hRi j
  obtain ⟨C,hC,hi'⟩ := hi δB (hδB₀.trans (min_le_right _ _)) rcut hcut Ri τ hRi le_rfl hτ
    (hτr.trans_le (min_le_right _ _)) j
  refine ⟨A+C,add_pos hA hC,?_⟩
  intro ε hε hεr
  have ho'' := ho' ε hε (hεr.trans_le (min_le_left _ _))
  have hi'' := hi' ε hε (hεr.trans_le (min_le_right _ _))
  rw [preferredWeightedRightIntegral_derivative_partition n d B hτ
    (preferredEqualityMultiplier Ri) (preferredEqualityMultiplier_smooth Ri) rcut hcut.2.2.1 j hε]
  calc
    _ ≤ ‖iteratedDeriv j (preferredWeightedRightIntegral n d B (preferredEqualityMultiplier Ri) τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖+
      ‖iteratedDeriv j (preferredWeightedRightIntegral n d B (fun θ => 1-preferredEqualityMultiplier Ri θ) τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖ := norm_add_le _ _
    _ ≤ A*(1+|Real.log ε|)+C := add_le_add ho'' hi''
    _ ≤ (A+C)*(1+|Real.log ε|) := by nlinarith [mul_nonneg hC.le (abs_nonneg (Real.log ε))]

end
end IsingBulk.Preferred22
