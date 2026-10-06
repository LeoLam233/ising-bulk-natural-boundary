import IsingBulk.Tail.AllBranchExteriorFarPairDerivative
import IsingBulk.Tail.AllBranchExteriorFarChartCutoff
import IsingBulk.Tail.AllBranchExteriorPairPartitionDerivatives

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff

/-- The complete actual far-chart derivative. The Gaussian numerator factor,
exponential-cutoff costs and the inverse separation are all explicit. -/
theorem allBranchExterior_far_chart_derivative {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ D c A ζ cN CN r : ℝ,
      1 ≤ D ∧ 0 < c ∧ 1 ≤ A ∧ 0 < ζ ∧ 0 < cN ∧ 0 < CN ∧ 0 < r ∧
      ∀ h : ℝ, 0 < h → h ≤ r → 2*h ≤ 1 → h ≤ d.thetaB/2 → h ≤ (Real.pi-d.thetaB)/2 →
      ∀ η δ : ℝ, ∀ hδ : 0 < δ, ∃ C₀ C₁ K : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧ 1 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ, 1 ≤ n → ∀ v : Fin (n+1), ∀ b ρ : ℝ,
      0 < b → b ≤ 1 → 0 < ρ → ρ ≤ 1 →
      B.original.separationThreshold*ε ≤ b/2 → 2*B.original.C₀*ε ≤ b/2 →
      let σ := ρ/Real.sqrt (n+1:ℝ)
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
        (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v))
        (radialParameter d.theta ε)‖ ≤
        ((n+1).choose 2:ℝ)*(allBranchExteriorFarLocalCost j (n+1) G C D c A
          (allBranchExteriorFarChartJetCost j (n+1) C₀ C₁ K b ρ) σ*
          (σ⁻¹*allBranchExteriorNearKernelCost B ε h (b/2) (2*h) ζ cN CN (n+1) 1)) := by
  obtain ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r₀,hD,hc,hA,hζ,hcN,hCN,hr₀,hbound⟩ :=
    allBranchExterior_far_pair_derivative B hcsmall j
  obtain ⟨rI,hrI,hpartition⟩ := allBranchExterior_pair_partition_bound d
  refine ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,min r₀ rI,hD,hc,hA,hζ,hcN,hCN,lt_min hr₀ hrI,?_⟩
  intro h hh hhr hh1 hhθ hhπ η δ hδ
  obtain ⟨C₀,C₁,K,hC₀,hC₁,hK,hjets⟩ := allBranchExterior_far_chart_cutoff_jets d.thetaB η d.alpha δ h hδ
    d.thetaB_pos d.thetaB_lt d.alpha_pos hh hhθ hhπ j
  refine ⟨C₀,C₁,K,hC₀,hC₁,hK,?_⟩
  intro ε hε hεr n hn v b ρ hb hb1 hρ hρ1 hsmall₁ hsmall₂
  dsimp only
  let σ := ρ/Real.sqrt (n+1:ℝ)
  have hσ : 0 < σ := div_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hsqrt : 1 ≤ Real.sqrt (n+1:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1:ℝ) ≤ n+1 by have := Nat.cast_nonneg n (α := ℝ); linarith)
  have hσ1 : σ ≤ 1 := (div_le_one (by positivity)).mpr (hρ1.trans hsqrt)
  have hW : 0 ≤ allBranchExteriorFarChartJetCost j (n+1) C₀ C₁ K b ρ := by
    unfold allBranchExteriorFarChartJetCost
    positivity
  apply hpartition ε hε (hεr.trans (min_le_right _ _)) n hn (j+1) _
    (allBranchExteriorFarChartWeight_smooth _ _ _ _ _ _ _ _ _ _) _ j
  · intro p q hpq
    apply hbound ε hε (hεr.trans (min_le_left _ _)) n p q v hpq h (b/2) (2*h) σ _ hh.le
      (hhr.trans (min_le_left _ _)) (by positivity) (by positivity) hσ hσ1 hW hsmall₁ hsmall₂ _
      (allBranchExteriorFarChartWeight_smooth _ _ _ _ _ _ _ _ _ _)
    · intro u hu
      have hs := allBranchExterior_far_chart_support d.thetaB η d.alpha δ h b ρ hδ hh hb hρ v u hu
      have hsep := allBranchExterior_far_diameter_pos (by omega : 0 < n+1) u ρ hρ hs.2.2.1
      refine ⟨hs.1,hs.2.1,?_,hs.2.2.2⟩
      simpa only [Nat.cast_add,Nat.cast_one] using hsep.1
    · intro u hu l hl
      have hs := allBranchExterior_far_chart_support d.thetaB η d.alpha δ h b ρ hδ hh hb hρ v u hu
      exact hjets (n+1) b ρ hb hb1 hρ hρ1 v u
        (allBranchExterior_far_diameter_pos (by omega : 0 < n+1) u ρ hρ hs.2.2.1).2 (hs.2.2.2.trans hh1) l hl
  · intro u hu
    have hs := allBranchExterior_far_chart_support d.thetaB η d.alpha δ h b ρ hδ hh hb hρ v u hu
    exact (mem_microcoreCube rI u).mpr (fun i => (hs.1 i).trans (hhr.trans (min_le_right _ _)))

end
end IsingBulk.Tail
