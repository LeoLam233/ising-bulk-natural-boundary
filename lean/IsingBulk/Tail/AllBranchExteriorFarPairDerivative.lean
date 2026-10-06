import IsingBulk.Tail.AllBranchExteriorPairDerivativeBound
import IsingBulk.Tail.AllBranchExteriorFarKernelMajorant
import IsingBulk.Tail.AllBranchExteriorFarSourceBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Set MeasureTheory Filter
open scoped ContDiff
set_option maxHeartbeats 800000

theorem allBranchExterior_far_pair_derivative {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ D c A ζ cN CN r : ℝ,
      1 ≤ D ∧ 0 < c ∧ 1 ≤ A ∧ 0 < ζ ∧ 0 < cN ∧ 0 < CN ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ,
      ∀ p q v : Fin (n+1), p ≠ q → ∀ R a S σ W : ℝ,
      0 ≤ R → R ≤ r → 0 < a → 0 < S → 0 < σ → σ ≤ 1 → 0 ≤ W →
      B.original.separationThreshold*ε ≤ a → 2*B.original.C₀*ε ≤ a →
      ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      (∀ u ∈ tsupport w, (∀ i, |u i| ≤ R) ∧ a ≤ |u v| ∧
        σ ≤ allBranchExteriorDiameter u ∧ allBranchExteriorDiameter u ≤ S) →
      (∀ u ∈ tsupport w, ∀ l : List (Fin (n+1)), l.length ≤ j →
          ‖cutoffJet l w u‖ ≤ W/allBranchExteriorDiameter u^l.length) →
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
        (fun u => w u*allBranchExteriorPairWeight (j+1) p q u)) (radialParameter d.theta ε)‖ ≤
        allBranchExteriorFarLocalCost j (n+1) G C D c A W σ*
          (σ⁻¹*allBranchExteriorNearKernelCost B ε R a S ζ cN CN (n+1) 1) := by
  obtain ⟨rI,hrI,hint⟩ := allBranchExterior_pair_derivative_bound d
  obtain ⟨G,C,hG,hC,D,c,A,rS,hD,hc,hA,hrS,hsource⟩ := allBranchExterior_far_source_budget d j
  obtain ⟨ζ,cN,CN,rK,hζ,hcN,hCN,hrK,hkernel⟩ := allBranchExterior_near_kernel_majorant_integral B hcsmall
  let r := min rI (min rS rK)
  have hr : 0 < r := lt_min hrI (lt_min hrS hrK)
  have hrI' : r ≤ rI := min_le_left _ _
  have hrS' : r ≤ rS := (min_le_right _ _).trans (min_le_left _ _)
  have hrK' : r ≤ rK := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r,hD,hc,hA,hζ,hcN,hCN,hr,?_⟩
  intro ε hε hεr n p q v hpq R a S σ W hR hRr ha hS hσ hσ1 hW hsmall₁ hsmall₂ w hw hsupp hjets
  let g := allBranchExteriorNearKernelMajorant d ε R a S v 1
  let L := allBranchExteriorFarLocalCost j (n+1) G C D c A W σ
  have hL : 0 ≤ L := by
    dsimp [L,allBranchExteriorFarLocalCost,allBranchExteriorFarNumeratorCost]
    positivity
  have hK : Integrable g ∧ (∫ u, g u) ≤ allBranchExteriorNearKernelCost B ε R a S ζ cN CN (n+1) 1 := by
    by_cases hv : v=p
    · subst v
      exact hkernel ε hε (hεr.trans hrK') n p q hpq R a S hR (hRr.trans hrK') ha hS hsmall₁ hsmall₂ 1 le_rfl
    · exact hkernel ε hε (hεr.trans hrK') n v p hv R a S hR (hRr.trans hrK') ha hS hsmall₁ hsmall₂ 1 le_rfl
  have hi := hint ε hε (hεr.trans hrI') n (j+1) p q hpq w hw
    (fun u hu => (mem_microcoreCube rI u).mpr (fun i => ((hsupp u hu).1 i).trans (hRr.trans hrI')))
    j (fun u => L*(σ⁻¹*g u)) ((hK.1.const_mul σ⁻¹).const_mul L) ?_
  · apply hi.trans
    rw [integral_const_mul,integral_const_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK.2 (inv_nonneg.mpr hσ.le)) hL
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
    have hs := hsupp u hsupport.1
    have hbound := hsource ε hε (hεr.trans hrS') n p q hpq h hh w hw u
      (fun i => (hs.1 i).trans (hRr.trans hrS')) hupq σ W hσ hσ1 hW hs.2.2.1
      (hjets u hsupport.1)
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (allBranchExterior_far_kernel_majorant_dominates d ε R a S σ hσ v u hs.1 hs.2.1 hs.2.2.1 hs.2.2.2) hL)
  · rw [allBranchExterior_source_sum_zero_off_support p q (-d.c₀*ε) d.thetaB _ _ j _ u hu,norm_zero]
    exact mul_nonneg hL (mul_nonneg (inv_nonneg.mpr hσ.le)
      (allBranchExterior_near_kernel_majorant_nonneg d ε R a S hS.le v 1 u))

end
end IsingBulk.Tail
