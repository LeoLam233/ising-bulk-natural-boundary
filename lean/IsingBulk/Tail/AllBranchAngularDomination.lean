import IsingBulk.Tail.AllBranchExteriorAngularWindow

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch
open scoped BigOperators

theorem original_allBranch_micro_exterior_domination (N : ℕ) (hN : 0 < N)
    (d : LocalBranchData) (η ε outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (hf : RegularSelector (constructedSelector d.thetaB η d.alpha))
    (hε : 0 < ε) (b ρ : ℝ)
    (hs : radialParameter d.theta ε ∈ dampingDomain (Real.exp (-d.c₀*ε))) (j : ℕ) :
    ‖iteratedDeriv j (originalSectorIntegral N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB outer inner ho hi none) (radialParameter d.theta ε)‖ ≤
    ‖iteratedDeriv j (microPartitionAngularIntegral N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB outer ho b ρ none) (radialParameter d.theta ε)‖ +
      allBranchExteriorAngularNorm N d η outer ε b ρ ho j := by
  rw [all_branch_micro_partition_derivative N hN _ hf (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])) d.tau_pos.le
    d.thetaB outer inner ho hi b ρ _ hs j,Fintype.sum_option,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun v _ => norm_add_le _ _)

end
end IsingBulk.Tail
