import IsingBulk.Tail.AllBranchExteriorPairDerivativeBound
import IsingBulk.Tail.AllBranchExteriorNearKernelMajorant
import IsingBulk.Tail.AllBranchExteriorNearSourceBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Set MeasureTheory Filter
open scoped ContDiff
set_option maxHeartbeats 800000

/-- Integrating the actual generated near-source sum, then removing its pair
puncture. Every kernel and regular-amplitude estimate is internal. The weight
support and jets are supplied by the actual chart cutoff in the next layer. -/
theorem allBranchExterior_near_pair_derivative {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ D c A ζ cN CN r : ℝ,
      1 ≤ D ∧ 0 < c ∧ 0 < A ∧ 0 < ζ ∧ 0 < cN ∧ 0 < CN ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ, 2*j+1 ≤ (n+1)*n →
      ∀ p q : Fin (n+1), p ≠ q → ∀ R a S H W : ℝ,
      0 ≤ R → R ≤ r → 0 < a → 0 < S → S ≤ 1 → 1 ≤ H →
      B.magnitudeUpper/Real.sqrt a ≤ H → H*S ≤ 1 → 0 ≤ W →
      B.original.separationThreshold*ε ≤ a → 2*B.original.C₀*ε ≤ a →
      ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      (∀ u ∈ tsupport w, (∀ i, |u i| ≤ R) ∧
        ((∀ i, a ≤ u i) ∨ (∀ i, u i ≤ -a)) ∧ allBranchExteriorDiameter u ≤ S) →
      (∀ u ∈ tsupport w, 0 < allBranchExteriorDiameter u →
        ∀ l : List (Fin (n+1)), l.length ≤ j →
          ‖cutoffJet l w u‖ ≤ W/allBranchExteriorDiameter u^l.length) →
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
        (fun u => w u*allBranchExteriorPairWeight (j+1) p q u)) (radialParameter d.theta ε)‖ ≤
        allBranchExteriorNearLocalCost j (n+1) G C D c A W H*
          allBranchExteriorNearKernelCost B ε R a S ζ cN CN (n+1) ((n+1)*n-2*j) := by
  obtain ⟨rI,hrI,hint⟩ := allBranchExterior_pair_derivative_bound d
  obtain ⟨G,C,hG,hC,D,c,A,rS,hD,hc,hA,hrS,hsource⟩ := allBranchExterior_near_source_budget B j
  obtain ⟨ζ,cN,CN,rK,hζ,hcN,hCN,hrK,hkernel⟩ := allBranchExterior_near_kernel_majorant_integral B hcsmall
  let r := min rI (min rS rK)
  have hr : 0 < r := lt_min hrI (lt_min hrS hrK)
  have hrI' : r ≤ rI := min_le_left _ _
  have hrS' : r ≤ rS := (min_le_right _ _).trans (min_le_left _ _)
  have hrK' : r ≤ rK := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r,hD,hc,hA,hζ,hcN,hCN,hr,?_⟩
  intro ε hε hεr n horder p q hpq R a S H W hR hRr ha hS hS1 hH hHmag hHS hW hsmall₁ hsmall₂ w hw hsupp hjets
  let Q := (n+1)*n-2*j
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  let g := allBranchExteriorNearKernelMajorant d ε R a S p Q
  let L := allBranchExteriorNearLocalCost j (n+1) G C D c A W H
  have hL : 0 ≤ L := by
    dsimp [L,allBranchExteriorNearLocalCost,allBranchExteriorNearNumeratorCost]
    positivity
  have hK : Integrable g ∧ (∫ u, g u) ≤ allBranchExteriorNearKernelCost B ε R a S ζ cN CN (n+1) Q :=
    hkernel ε hε (hεr.trans hrK') n p q hpq R a S hR (hRr.trans hrK') ha hS hsmall₁ hsmall₂ Q hQ
  have hi := hint ε hε (hεr.trans hrI') n (j+1) p q hpq w hw
    (fun u hu => (mem_microcoreCube rI u).mpr (fun i => ((hsupp u hu).1 i).trans (hRr.trans hrI')))
    j (fun u => L*g u) (hK.1.const_mul L) ?_
  · apply hi.trans
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hK.2 hL
  intro h hh
  apply Eventually.of_forall
  intro u
  by_cases hu : u ∈ tsupport (allBranchSingleTruncatedWeight (j+1) h p q w)
  · have hsupport := allBranchSingleTruncatedWeight_support (j+1) hh p q w hu
    have hupq : u p ≠ u q := by
      intro he
      have hh' := hsupport.2
      rw [he,sub_self,abs_zero] at hh'
      linarith
    have hdiam : 0 < allBranchExteriorDiameter u :=
      (abs_pos.mpr (sub_ne_zero.mpr hupq)).trans_le (allBranchExterior_pair_le_diameter u p q)
    have hs := hsupp u hsupport.1
    have hbound := hsource ε hε (hεr.trans hrS') n (by omega) p q hpq h hh w hw u
      (fun i => (hs.1 i).trans (hRr.trans hrS')) hupq a H W ha hH hHmag hW hs.2.1
      (hs.2.2.trans hS1) ((mul_le_mul_of_nonneg_left hs.2.2 (by linarith : 0 ≤ H)).trans hHS)
      (hjets u hsupport.1 hdiam)
    apply hbound.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (allBranchExterior_near_kernel_majorant_dominates d ε R a S ha p Q u hs.1 hdiam hs.2.2 hs.2.1) hL
  · rw [allBranchExterior_source_sum_zero_off_support p q (-d.c₀*ε) d.thetaB _ _ j _ u hu,norm_zero]
    exact mul_nonneg hL (allBranchExterior_near_kernel_majorant_nonneg d ε R a S hS.le p Q u)

end
end IsingBulk.Tail
