import IsingBulk.Tail.AllBranchExteriorNearPairDerivative
import IsingBulk.Tail.AllBranchExteriorNearChartSupport

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff

/-- The actual compact all-branch near chart, with a named exterior anchor,
has a pairwise derivative bound whose constants are fixed before the equality
scale. No unspecified source-jet or integrable-majorant premise remains. -/
theorem allBranchExterior_near_chart_pair_derivative {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ D c A ζ cN CN r : ℝ,
      1 ≤ D ∧ 0 < c ∧ 0 < A ∧ 0 < ζ ∧ 0 < cN ∧ 0 < CN ∧ 0 < r ∧
      ∀ h : ℝ, 0 < h → h ≤ r → h ≤ d.thetaB/2 → h ≤ (Real.pi-d.thetaB)/2 →
      ∀ η δ : ℝ, ∀ hδ : 0 < δ, ∃ C₀ C₁ K : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧ 1 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ, 2*j+1 ≤ (n+1)*n →
      ∀ p q v : Fin (n+1), p ≠ q → ∀ b ρ H : ℝ,
      0 < b → b ≤ 1 → 0 < ρ → 4*ρ ≤ 1 → 2*ρ ≤ b/8 → 1 ≤ H →
      B.magnitudeUpper/Real.sqrt (b/4) ≤ H → H*(4*ρ) ≤ 1 →
      B.original.separationThreshold*ε ≤ b/4 → 2*B.original.C₀*ε ≤ b/4 →
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
        (fun u => allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v u*
          allBranchExteriorPairWeight (j+1) p q u)) (radialParameter d.theta ε)‖ ≤
        allBranchExteriorNearLocalCost j (n+1) G C D c A
          (allBranchExteriorNearChartJetCost j (n+1) C₀ C₁ K b) H*
          allBranchExteriorNearKernelCost B ε h (b/4) (4*ρ) ζ cN CN (n+1) ((n+1)*n-2*j) := by
  obtain ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r,hD,hc,hA,hζ,hcN,hCN,hr,hbound⟩ :=
    allBranchExterior_near_pair_derivative B hcsmall j
  refine ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r,hD,hc,hA,hζ,hcN,hCN,hr,?_⟩
  intro h hh hhr hhθ hhπ η δ hδ
  obtain ⟨C₀,C₁,K,hC₀,hC₁,hK,hjets⟩ := allBranchExterior_near_chart_cutoff_jets d.thetaB η d.alpha δ h hδ
    d.thetaB_pos d.thetaB_lt d.alpha_pos hh hhθ hhπ j
  refine ⟨C₀,C₁,K,hC₀,hC₁,hK,?_⟩
  intro ε hε hεr n horder p q v hpq b ρ H hb hb1 hρ hρ1 hscale hH hHmag hHρ hsmall₁ hsmall₂
  have hW : 0 ≤ allBranchExteriorNearChartJetCost j (n+1) C₀ C₁ K b := by
    unfold allBranchExteriorNearChartJetCost
    positivity
  apply hbound ε hε hεr n horder p q hpq h (b/4) (4*ρ) H _ hh.le hhr
    (by positivity) (by positivity) hρ1 hH hHmag hHρ hW hsmall₁ hsmall₂ _
    (allBranchExteriorNearChartWeight_smooth _ _ _ _ _ _ _ _ _ _)
  · intro u hu
    have hs := allBranchExterior_near_chart_support d.thetaB η d.alpha δ h b ρ hδ hh hb hρ v u hu
    exact ⟨hs.1,allBranchExterior_near_chart_common_sign d.thetaB η d.alpha δ h b ρ hδ hh hb hρ hscale v u hu,hs.2.2.2⟩
  · intro u hu hdiam l hl
    have hs := allBranchExterior_near_chart_support d.thetaB η d.alpha δ h b ρ hδ hh hb hρ v u hu
    exact hjets (n+1) b ρ hb hb1 hρ (by linarith) v u hdiam hs.2.2.2 l hl

end
end IsingBulk.Tail
