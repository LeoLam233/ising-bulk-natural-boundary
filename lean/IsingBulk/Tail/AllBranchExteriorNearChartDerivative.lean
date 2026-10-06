import IsingBulk.Tail.AllBranchExteriorNearChartPairDerivative
import IsingBulk.Tail.AllBranchExteriorPairPartitionDerivatives

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff

/-- The full actual near-chart derivative, after summing the finite pair
partition. The surviving collision power is N(N-1)-2j; the kernel cost
contains one inverse diameter, which is retained explicitly. -/
theorem allBranchExterior_near_chart_derivative {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ D c A ζ cN CN r : ℝ,
      1 ≤ D ∧ 0 < c ∧ 0 < A ∧ 0 < ζ ∧ 0 < cN ∧ 0 < CN ∧ 0 < r ∧
      ∀ h : ℝ, 0 < h → h ≤ r → h ≤ d.thetaB/2 → h ≤ (Real.pi-d.thetaB)/2 →
      ∀ η δ : ℝ, ∀ hδ : 0 < δ, ∃ C₀ C₁ K : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧ 1 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ, 2*j+1 ≤ (n+1)*n →
      ∀ v : Fin (n+1), ∀ b ρ H : ℝ,
      0 < b → b ≤ 1 → 0 < ρ → 4*ρ ≤ 1 → 2*ρ ≤ b/8 → 1 ≤ H →
      B.magnitudeUpper/Real.sqrt (b/4) ≤ H → H*(4*ρ) ≤ 1 →
      B.original.separationThreshold*ε ≤ b/4 → 2*B.original.C₀*ε ≤ b/4 →
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
        (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v))
        (radialParameter d.theta ε)‖ ≤
        ((n+1).choose 2:ℝ)*(allBranchExteriorNearLocalCost j (n+1) G C D c A
          (allBranchExteriorNearChartJetCost j (n+1) C₀ C₁ K b) H*
          allBranchExteriorNearKernelCost B ε h (b/4) (4*ρ) ζ cN CN (n+1) ((n+1)*n-2*j)) := by
  obtain ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r₀,hD,hc,hA,hζ,hcN,hCN,hr₀,hbound⟩ :=
    allBranchExterior_near_chart_pair_derivative B hcsmall j
  obtain ⟨rI,hrI,hpartition⟩ := allBranchExterior_pair_partition_bound d
  refine ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,min r₀ rI,hD,hc,hA,hζ,hcN,hCN,lt_min hr₀ hrI,?_⟩
  intro h hh hhr hhθ hhπ η δ hδ
  obtain ⟨C₀,C₁,K,hC₀,hC₁,hK,hpair⟩ := hbound h hh (hhr.trans (min_le_left _ _)) hhθ hhπ η δ hδ
  refine ⟨C₀,C₁,K,hC₀,hC₁,hK,?_⟩
  intro ε hε hεr n horder v b ρ H hb hb1 hρ hρ1 hscale hH hHmag hHρ hsmall₁ hsmall₂
  have hn : 1 ≤ n := by nlinarith
  apply hpartition ε hε (hεr.trans (min_le_right _ _)) n hn (j+1) _
    (allBranchExteriorNearChartWeight_smooth _ _ _ _ _ _ _ _ _ _) _ j
  · intro p q hpq
    exact hpair ε hε (hεr.trans (min_le_left _ _)) n horder p q v hpq b ρ H
      hb hb1 hρ hρ1 hscale hH hHmag hHρ hsmall₁ hsmall₂
  · intro u hu
    have hs := allBranchExterior_near_chart_support d.thetaB η d.alpha δ h b ρ hδ hh hb hρ v u hu
    exact (mem_microcoreCube rI u).mpr (fun i => (hs.1 i).trans (hhr.trans (min_le_right _ _)))

end
end IsingBulk.Tail
