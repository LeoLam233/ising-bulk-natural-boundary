import IsingBulk.HT.Contour.SignedPositiveSpectators
import IsingBulk.Tail.AllBranchExteriorWeightedPositive

/-! A positive collision power absorbs the extreme-pair Jacobian loss.
The positive-coordinate cell has no fixed lower gap; injectivity is recovered
from the existing separated cells for each pair of points. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory
open scoped BigOperators

theorem signed_positive_power_master_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a D R α β shiftY shiftZ : ℝ) (P : ℕ) (p q : Fin N) (hpq : p ≠ q)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hD : 0 < D)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    let L := fun t => ‖deriv (originalPhase d ε) t‖
    let k := shiftedWeightedPhaseSpectatorKernel p q α β shiftY shiftZ L
    let T := allBranchExteriorCoordinateMap d ε p q
    let S := allBranchExteriorPositiveGapCell p q R a D
    IntegrableOn (fun u => (u q-u p)^(P+1)*
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*k (T u)) S ∧
    (∫ u in S, (u q-u p)^(P+1)*
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*k (T u)) ≤
      (D^(P+1)*allBranchExteriorPositiveCost B a D)*
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2)) := by
  dsimp only
  let S := allBranchExteriorPositiveGapCell p q R a D
  let L := fun t => ‖deriv (originalPhase d ε) t‖
  let k := shiftedWeightedPhaseSpectatorKernel p q α β shiftY shiftZ L
  let T := allBranchExteriorCoordinateMap d ε p q
  let T' := fun u => twoPhaseUpdateDeriv (coordinateSumLinear N) (allBranchExteriorTotalDerivative d ε u) p q
  have hL := allBranchExterior_arclength_continuousOn B ε R hε hεr hRB
  have hLint := (B.length_restrict ε hε hεr (Icc (-R) R) (by
    intro t ht
    constructor <;> linarith [ht.1,ht.2])).2
  have hki := shifted_weighted_phase_spectator_kernel_integral hpq shiftY shiftZ L B.lengthC B.lengthC_pos.le
    (fun _ => norm_nonneg _) hR hα hα1 hβ hβ1 hL hLint
  have hd (u : Fin N → ℝ) (hu : u ∈ S) : HasFDerivWithinAt T (T' u) S u :=
    (allBranchExterior_coordinate_hasFDerivAt B ε hε hεr u
      (fun i => ⟨hu.1.1.1 i,(hu.1.1.2 i).trans hRB⟩) p q).hasFDerivWithinAt
  have hw : ContinuousOn (fun u : Fin N → ℝ => (u q-u p)^(P+1)*
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖) S := by
    have hp : ContinuousOn (fun u : Fin N → ℝ => L (u p)) S :=
      hL.comp (continuous_apply p).continuousOn (fun u hu =>
        ⟨by linarith [hu.1.1.1 p],hu.1.1.2 p⟩)
    have hq : ContinuousOn (fun u : Fin N → ℝ => L (u q)) S :=
      hL.comp (continuous_apply q).continuousOn (fun u hu =>
        ⟨by linarith [hu.1.1.1 q],hu.1.1.2 q⟩)
    simp_rw [norm_mul]
    exact (((continuous_apply q).sub (continuous_apply p)).pow (P+1)).continuousOn.mul (hp.mul hq)
  have hC : 0 ≤ D^(P+1)*allBranchExteriorPositiveCost B a D :=
    mul_nonneg (pow_nonneg hD.le _) (allBranchExterior_positive_cost_nonneg B ha hD)
  have hratio (u : Fin N → ℝ) (hu : u ∈ S) :
      (u q-u p)^(P+1)*‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖ ≤
        (D^(P+1)*allBranchExteriorPositiveCost B a D)*|(T' u).det| := by
    have hh := allBranchExterior_positive_jacobian_ratio B ε a (u q-u p) hε hεr ha hu.2.1
      hsmall₁ hsmall₂ (u p,u q) ⟨hu.1.1.1 p,(hu.1.1.2 q).trans hRB,hu.1.2.1,le_rfl⟩
    have hpair : ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖ ≤
        allBranchExteriorPositiveCost B a (u q-u p)*|(T' u).det| := by
      simpa only [T',allBranchExterior_coordinate_det d ε u p q hpq,allBranchExterior_positive_det] using hh
    calc
      _ ≤ (u q-u p)^(P+1)*(allBranchExteriorPositiveCost B a (u q-u p)*|(T' u).det|) :=
        mul_le_mul_of_nonneg_left hpair (pow_nonneg hu.2.1.le _)
      _ = ((u q-u p)^(P+1)*allBranchExteriorPositiveCost B a (u q-u p))*|(T' u).det| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (allBranchExterior_positive_power_absorption B ha hu.2.1 hu.2.2 P) (abs_nonneg _)
  have himage : T '' S ⊆ phaseSpectatorBox p q R := by
    rintro _ ⟨u,hu,rfl⟩
    exact allBranchExterior_coordinate_image_on_subradius B ε a 0 R p q hε hεr hR hRB hRπ ⟨u,hu.1,rfl⟩
  obtain ⟨hi,hb⟩ := injective_coordinate_weighted_coarea_on
    (allBranchExterior_positive_gap_cell_measurable p q R a D) T T' hd
    (allBranchExterior_positive_gap_injective B ε a D R p q hpq hε hεr ha hRB hsmall₁ hsmall₂)
    himage _ k hw (shiftedWeightedPhaseSpectatorKernel_continuousOn p q hα hβ shiftY shiftZ L hL)
    (shiftedWeightedPhaseSpectatorKernel_nonneg p q α β shiftY shiftZ L (fun _ => norm_nonneg _)) hki.1 hC
    (fun u hu => mul_nonneg (pow_nonneg hu.2.1.le _) (norm_nonneg _)) hratio
  exact ⟨hi,hb.trans (mul_le_mul_of_nonneg_left hki.2 hC)⟩

end
end IsingBulk.HT.Contour
