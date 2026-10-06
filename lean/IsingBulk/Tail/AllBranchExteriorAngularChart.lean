import IsingBulk.Tail.MicrocoreAngularPartition
import IsingBulk.Tail.AllBranchExteriorFarChartCutoff
import IsingBulk.Tail.AllBranchExteriorTruncatedIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped BigOperators Topology

theorem microPartitionAngularIntegral_some_box (N : ℕ) (d : LocalBranchData)
    (η δ ε b ρ : ℝ) (hδ : 0 < δ) (v : Fin N) (k : Fin 2) :
    microPartitionAngularIntegral N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,k)) =
    allBranchBoxIntegral N d η δ ε hδ
      (fun u => (microPartitionWeight b ρ (some (v,k)) u : ℝ)) := by
  funext s
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp [microPartitionAngularIntegral,weightedAngularIntegral,allBranchAngularWeight,
    allBranchBoxIntegral]
  push_cast
  ring

theorem allBranchChartIntegral_near_original (n : ℕ) (d : LocalBranchData)
    (η δ h ε b ρ : ℝ) (hδ : 0 < δ) (v : Fin (n+1)) :
    allBranchChartIntegral (n+1) d η δ h ε hδ
      (fun u => (microPartitionWeight b ρ (some (v,0)) u : ℝ)) =
    allBranchOriginalWeightedIntegral n d ε
      (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v) := by
  funext s
  unfold allBranchChartIntegral allBranchOriginalWeightedIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [microPartitionWeight,ite_true,allBranchExteriorNearChartWeight,
    Complex.ofReal_mul]
  ring

theorem allBranchChartIntegral_far_original (n : ℕ) (d : LocalBranchData)
    (η δ h ε b ρ : ℝ) (hδ : 0 < δ) (v : Fin (n+1)) :
    allBranchChartIntegral (n+1) d η δ h ε hδ
      (fun u => (microPartitionWeight b ρ (some (v,1)) u : ℝ)) =
    allBranchOriginalWeightedIntegral n d ε
      (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v) := by
  funext s
  unfold allBranchChartIntegral allBranchOriginalWeightedIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [microPartitionWeight,show (1:Fin 2) ≠ 0 by decide,ite_false,
    allBranchExteriorFarChartWeight,Complex.ofReal_mul]
  ring

theorem allBranchExterior_angular_chart_derivatives (d : LocalBranchData)
    (h : ℝ) (hh : 0 < h) (hhb : h ≤ d.thetaB/2) (hhpi : h ≤ (Real.pi-d.thetaB)/2)
    (hα : d.alpha < Real.sin d.thetaB/4) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ (n : ℕ) (η ε b ρ : ℝ), 0 < ε → ∀ (v : Fin (n+1)) (s : ℂ),
      s ∈ dampingDomain (Real.exp (-d.c₀*ε)) → ∀ j : ℕ,
      (iteratedDeriv j (microPartitionAngularIntegral (n+1) (constructedSelector d.thetaB η d.alpha)
        (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,0))) s =
        iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
          (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v)) s) ∧
      (iteratedDeriv j (microPartitionAngularIntegral (n+1) (constructedSelector d.thetaB η d.alpha)
        (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,1))) s =
        iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
          (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v)) s) := by
  obtain ⟨δ₀,hδ₀,heq⟩ := all_branch_box_chart_derivatives d h hh hhb hhpi hα
  refine ⟨δ₀,hδ₀,?_⟩
  intro δ hδ hδsmall n η ε b ρ hε v s hs j
  constructor
  · rw [microPartitionAngularIntegral_some_box,
      heq δ hδ hδsmall (n+1) η ε hε _ s hs j,allBranchChartIntegral_near_original]
  · rw [microPartitionAngularIntegral_some_box,
      heq δ hδ hδsmall (n+1) η ε hε _ s hs j,allBranchChartIntegral_far_original]

end
end IsingBulk.Tail
