import IsingBulk.HT.Contour.SignedAngleBoxChart
import IsingBulk.HT.Lie.SignedPhysicalIntegral
import IsingBulk.Tail.AllBranchExteriorAngularChart

/-! Literal signed near/far angular source sectors and their exact compact
chart derivatives. The sole outside factorial and every real partition
weight agree with the physical source before differentiating. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie MeasureTheory Set
open scoped BigOperators Topology

def signedMicroPartitionAngularIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    (r tau b delta : ℝ) (hd : 0 < delta) (a rho : ℝ)
    (label : Option (Fin N × Fin 2)) (s : ℂ) : ℂ :=
  ∫ theta in angleBox N, (allBranchAngularWeight f b delta hd theta *
    (microPartitionWeight a rho label (fun i => theta i+b-2*Real.pi):ℂ))*
      signedPulledDensity σ f r tau 0 s theta

theorem signedMicroPartitionAngularIntegral_some_box (σ : ℂ) (N : ℕ) (d : LocalBranchData)
    (η δ ε b ρ : ℝ) (hδ : 0 < δ) (v : Fin N) (k : Fin 2) :
    signedMicroPartitionAngularIntegral σ N (constructedSelector d.thetaB η d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,k)) =
    signedAllBranchBoxIntegral σ N d η δ ε hδ
      (fun u => (microPartitionWeight b ρ (some (v,k)) u : ℝ)) := by
  funext s
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp [signedMicroPartitionAngularIntegral,allBranchAngularWeight,
    signedAllBranchBoxIntegral]
  push_cast
  ring

theorem signedAllBranchChartIntegral_near_original (σ : ℂ) (n : ℕ) (d : LocalBranchData)
    (η δ h ε b ρ : ℝ) (hδ : 0 < δ) (v : Fin (n+1)) :
    signedAllBranchChartIntegral σ (n+1) d η δ h ε hδ
      (fun u => (microPartitionWeight b ρ (some (v,0)) u : ℝ)) =
    signedOriginalWeightedIntegral σ n d ε
      (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v) := by
  funext s
  unfold signedAllBranchChartIntegral signedOriginalWeightedIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [microPartitionWeight,ite_true,allBranchExteriorNearChartWeight,
    Complex.ofReal_mul]
  ring

theorem signedAllBranchChartIntegral_far_original (σ : ℂ) (n : ℕ) (d : LocalBranchData)
    (η δ h ε b ρ : ℝ) (hδ : 0 < δ) (v : Fin (n+1)) :
    signedAllBranchChartIntegral σ (n+1) d η δ h ε hδ
      (fun u => (microPartitionWeight b ρ (some (v,1)) u : ℝ)) =
    signedOriginalWeightedIntegral σ n d ε
      (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v) := by
  funext s
  unfold signedAllBranchChartIntegral signedOriginalWeightedIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [microPartitionWeight,show (1:Fin 2) ≠ 0 by decide,ite_false,
    allBranchExteriorFarChartWeight,Complex.ofReal_mul]
  ring

theorem signed_allBranchExterior_angular_chart_derivatives (d : LocalBranchData)
    (h : ℝ) (hh : 0 < h) (hhb : h ≤ d.thetaB/2) (hhpi : h ≤ (Real.pi-d.thetaB)/2)
    (hα : d.alpha < Real.sin d.thetaB/4) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ (σ : ℂ) (n : ℕ) (η ε b ρ : ℝ) (v : Fin (n+1)) (s : ℂ) (j : ℕ),
      (iteratedDeriv j (signedMicroPartitionAngularIntegral σ (n+1) (constructedSelector d.thetaB η d.alpha)
        (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,0))) s =
        iteratedDeriv j (signedOriginalWeightedIntegral σ n d ε
          (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v)) s) ∧
      (iteratedDeriv j (signedMicroPartitionAngularIntegral σ (n+1) (constructedSelector d.thetaB η d.alpha)
        (Real.exp (-d.c₀*ε)) d.tau d.thetaB δ hδ b ρ (some (v,1))) s =
        iteratedDeriv j (signedOriginalWeightedIntegral σ n d ε
          (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v)) s) := by
  obtain ⟨δ₀,hδ₀,heq⟩ := signed_all_branch_box_chart_derivatives d h hh hhb hhpi hα
  refine ⟨δ₀,hδ₀,?_⟩
  intro δ hδ hδsmall σ n η ε b ρ v s j
  constructor
  · rw [signedMicroPartitionAngularIntegral_some_box,
      heq δ hδ hδsmall σ (n+1) η ε _ s j,signedAllBranchChartIntegral_near_original]
  · rw [signedMicroPartitionAngularIntegral_some_box,
      heq δ hδ hδsmall σ (n+1) η ε _ s j,signedAllBranchChartIntegral_far_original]

end
end IsingBulk.HT.Contour
