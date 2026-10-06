import IsingBulk.Tail.AllBranchExteriorSingleTruncation
import IsingBulk.Tail.AllBranchExteriorWeightedPole

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Set
open scoped ContDiff

/-- The artificial pair guard has a pole bound independent of its removal
scale. Only the real spatial cutoff jets remain as inputs to this helper. -/
theorem allBranchExterior_single_truncated_pole (d : LocalBranchData) (M J : ℕ)
    (hM : 0 < M) (hJ : J < 2*M) :
    ∃ C : ℕ, 0 < C ∧ ∃ D c r : ℝ, 1 ≤ D ∧ 0 < c ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ N : ℕ, 1 ≤ N →
      ∀ h : ℝ, 0 < h → ∀ p q : Fin N, ∀ u : Fin N → ℝ,
      (∀ i, |u i| ≤ r) → u p ≠ u q →
      ∀ w : (Fin N → ℝ) → ℝ, ContDiff ℝ ∞ w → ∀ A : ℝ, 0 ≤ A →
      (∀ k : List (Fin N), k.length ≤ J →
        ‖cutoffJet k w u‖ ≤ A/allBranchExteriorDiameter u^k.length) →
      ∀ l : List (Fin N), l.length ≤ J → ∀ m : ℕ, m+l.length ≤ 2*M →
      ‖cutoffJet l (allBranchSingleTruncatedWeight M h p q w) u‖/
        ‖originalPhase d ε (u p)-originalPhase d ε (u q)‖^m ≤
        ((2:ℝ)^J*(((2:ℝ)^J*(C:ℝ)*(N:ℝ)^C*D)*(c⁻¹)^m)*A)/
          allBranchExteriorDiameter u^(m+l.length) := by
  obtain ⟨C,hC,D,c,r,hD,hc,hr,hguard⟩ := allBranchGuardedPairWeight_pole_uniform d M J hM hJ
  refine ⟨C,hC,D,c,r,hD,hc,hr,?_⟩
  intro ε hε hεr N hN h hh p q u hu hpq w hw A hA hwjets l hl m hm
  have hdiam : 0 < allBranchExteriorDiameter u :=
    (abs_pos.mpr (sub_ne_zero.mpr hpq)).trans_le (allBranchExterior_pair_le_diameter u p q)
  let G := ((2:ℝ)^J*(C:ℝ)*(N:ℝ)^C*D)*(c⁻¹)^m
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hfj (k : List (Fin N)) (hk : k.length ≤ l.length) :
      ‖cutoffJet k (allBranchGuardedPairWeight M h p q) u‖/
        ‖originalPhase d ε (u p)-originalPhase d ε (u q)‖^m ≤ G/allBranchExteriorDiameter u^(m+k.length) := by
    simpa only [G,Nat.add_comm] using hguard ε hε hεr N hN h hh p q u hu hpq k (hk.trans hl) m (by omega)
  have hb := allBranchExterior_weighted_pole_bound (allBranchGuardedPairWeight M h p q) w isOpen_univ
    (fun _ _ => (allBranchGuardedPairWeight_smooth M hh p q).contDiffAt)
    (fun _ _ => hw.contDiffAt) u (mem_univ u) l m (allBranchExteriorDiameter u)
    ‖originalPhase d ε (u p)-originalPhase d ε (u q)‖ G A hdiam (norm_nonneg _) hG hA
    hfj (fun k hk => hwjets k (hk.trans hl))
  have he : allBranchSingleTruncatedWeight M h p q w=
      fun x => allBranchGuardedPairWeight M h p q x*w x := by
    funext x
    exact mul_comm _ _
  rw [he]
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hdiam.le _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hl) hG) hA

end
end IsingBulk.Tail
