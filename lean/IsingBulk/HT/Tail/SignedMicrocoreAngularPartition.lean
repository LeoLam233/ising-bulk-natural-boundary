import IsingBulk.HT.Tail.SignedAngularFinitePartition
import IsingBulk.HT.Tail.SignedSectorIntegralDecomposition
import IsingBulk.HT.Tail.NegativeSectorMicrocoreAngleBox
import IsingBulk.HT.Lie.SignedAngularWindow
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.HT.Lie IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped BigOperators Topology ContDiff
theorem signed_all_branch_micro_partition_derivative (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (a rho : ℝ)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi none) s =
      ∑ label : Option (Fin N × Fin 2),
        iteratedDeriv j (signedMicroPartitionAngularIntegral σ N f r tau b outer ho a rho label) s := by
  have hmap : Continuous (fun theta : Fin N → ℝ => fun i => theta i+b-2*Real.pi) := by fun_prop
  apply signed_weightedAngularIntegral_finite_partition_jets σ hσ N hN f hf hr hr1 htau le_rfl
    (allBranchAngularWeight f b outer ho) (allBranchAngularWeight_continuous f hf b outer ho)
    (fun label theta => (microPartitionWeight a rho label (fun i => theta i+b-2*Real.pi):ℝ))
  · intro label
    exact Complex.continuous_ofReal.comp ((microPartitionWeight_smooth a rho label).continuous.comp hmap)
  · intro theta
    rw [← Complex.ofReal_sum,microPartitionWeight_sum,Complex.ofReal_one]
  · exact hs

theorem negativeMicroPartitionAngularIntegral_none (n : ℕ) (d : LocalBranchData)
    (eta delta : ℝ) (hd : 0 < delta) (eps a rho : ℝ) :
    signedMicroPartitionAngularIntegral (-1) (n+2) (constructedSelector d.thetaB eta d.alpha)
      (Real.exp (-d.c₀*eps)) d.tau d.thetaB delta hd a rho none =
        negativeAngleBoxMicrocoreIntegral n d eta delta hd eps a := by
  funext s
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta _
  dsimp [signedMicroPartitionAngularIntegral,allBranchAngularWeight,
    microPartitionWeight,negativeAngleBoxMicrocoreIntegral,negativePulledDensity]
  push_cast
  ring

theorem signed_original_allBranch_micro_exterior_domination (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (d : LocalBranchData) (η ε outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (hf : RegularSelector (constructedSelector d.thetaB η d.alpha))
    (hε : 0 < ε) (b ρ : ℝ)
    (hs : radialParameter d.theta ε ∈ dampingDomain (Real.exp (-d.c₀*ε))) (j : ℕ) :
    ‖iteratedDeriv j (signedOriginalSectorIntegral σ N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB outer inner ho hi none) (radialParameter d.theta ε)‖ ≤
    ‖iteratedDeriv j (signedMicroPartitionAngularIntegral σ N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB outer ho b ρ none) (radialParameter d.theta ε)‖ +
      signedExteriorAngularNorm σ N d η outer ε b ρ ho j := by
  rw [signed_all_branch_micro_partition_derivative σ hσ N hN _ hf (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])) d.tau_pos.le
    d.thetaB outer inner ho hi b ρ _ hs j,Fintype.sum_option,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun v _ => norm_add_le _ _)

end
end IsingBulk.HT.Tail
