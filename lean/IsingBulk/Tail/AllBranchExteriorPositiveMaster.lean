import IsingBulk.Tail.AllBranchSpectatorCoarea
import IsingBulk.Tail.AllBranchExteriorCoordinateCell
import IsingBulk.Tail.AllBranchExteriorPositiveJacobian

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

theorem allBranchExterior_arclength_continuousOn {d : LocalBranchData} (B : BranchEstimates d)
    (ε R : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (hR : R ≤ B.r) :
    ContinuousOn (fun t => ‖deriv (originalPhase d ε) t‖) (Icc (-R) R) := by
  intro t ht
  have htR : |t| ≤ B.r := (abs_le.mpr ht).trans hR
  obtain ⟨hr,hi⟩ := B.quadrant ε t hε hεr htR
  exact (currentPhase_second_hasDerivAt d ε 0 t hr hi).continuousAt.norm.continuousWithinAt

theorem allBranchExterior_positive_master_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a σ R α β : ℝ) (p q : Fin N) (hpq : p ≠ q)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    let L := fun t => ‖deriv (originalPhase d ε) t‖
    let k := weightedPhaseSpectatorKernel p q α β L
    let T := allBranchExteriorCoordinateMap d ε p q
    let S := allBranchExteriorCoordinateCell p q R a σ
    IntegrableOn (fun u => ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*k (T u)) S ∧
    (∫ u in S, ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*k (T u)) ≤
      allBranchExteriorPositiveCost B a σ *
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2)) := by
  dsimp only
  let S := allBranchExteriorCoordinateCell p q R a σ
  let L := fun t => ‖deriv (originalPhase d ε) t‖
  let k := weightedPhaseSpectatorKernel p q α β L
  let T := allBranchExteriorCoordinateMap d ε p q
  let T' := fun u => twoPhaseUpdateDeriv (coordinateSumLinear N) (allBranchExteriorTotalDerivative d ε u) p q
  have hsub : S ⊆ allBranchExteriorCoordinateCell p q B.r a σ := by
    intro u hu
    exact ⟨⟨hu.1.1,fun i => (hu.1.2 i).trans hRB⟩,hu.2⟩
  have hL := allBranchExterior_arclength_continuousOn B ε R hε hεr hRB
  have hLint := (B.length_restrict ε hε hεr (Icc (-R) R) (by
    intro t ht
    constructor <;> linarith [ht.1,ht.2])).2
  have hki := weighted_phase_spectator_kernel_integral hpq L B.lengthC B.lengthC_pos.le
    (fun _ => norm_nonneg _) hR hα hα1 hβ hβ1 hL hLint
  have hd (u : Fin N → ℝ) (hu : u ∈ S) : HasFDerivWithinAt T (T' u) S u :=
    (allBranchExterior_coordinate_hasFDerivAt B ε hε hεr u
      (fun i => ⟨hu.1.1 i,(hu.1.2 i).trans hRB⟩) p q).hasFDerivWithinAt
  have hw : ContinuousOn (fun u : Fin N → ℝ =>
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖) S := by
    have hp : ContinuousOn (fun u : Fin N → ℝ => L (u p)) S := hL.comp (continuous_apply p).continuousOn (fun u hu =>
      (show u p ∈ Icc (-R) R from ⟨by linarith [hu.1.1 p],hu.1.2 p⟩))
    have hq : ContinuousOn (fun u : Fin N → ℝ => L (u q)) S := hL.comp (continuous_apply q).continuousOn (fun u hu =>
      (show u q ∈ Icc (-R) R from ⟨by linarith [hu.1.1 q],hu.1.2 q⟩))
    have he : (fun u : Fin N → ℝ => ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖)=
        (fun u => L (u p))*(fun u => L (u q)) := by
      funext u
      exact norm_mul _ _
    rw [he]
    exact hp.mul hq
  have hC : 0 ≤ allBranchExteriorPositiveCost B a σ := by
    have := B.original.k_pos
    have := B.original.a_pos
    unfold allBranchExteriorPositiveCost
    positivity
  have hratio (u : Fin N → ℝ) (hu : u ∈ S) :
      ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖ ≤
        allBranchExteriorPositiveCost B a σ*|(T' u).det| := by
    have hh := allBranchExterior_positive_jacobian_ratio B ε a σ hε hεr ha hσ hsmall₁ hsmall₂
      (u p,u q) ⟨hu.1.1 p,(hu.1.2 q).trans hRB,hu.2.1,hu.2.2⟩
    simpa only [T',allBranchExterior_coordinate_det d ε u p q hpq,allBranchExterior_positive_det] using hh
  obtain ⟨hi,hb⟩ := injective_coordinate_weighted_coarea_on
    (allBranchExterior_coordinate_cell_measurable p q R a σ) T T' hd
    ((allBranchExterior_coordinate_injective B ε a σ p q hpq hε hεr ha hσ hsmall₁ hsmall₂).mono hsub)
    (allBranchExterior_coordinate_image_on_subradius B ε a σ R p q hε hεr hR hRB hRπ)
    _ k hw (weightedPhaseSpectatorKernel_continuousOn p q hα hβ L hL)
    (weightedPhaseSpectatorKernel_nonneg p q α β L (fun _ => norm_nonneg _)) hki.1 hC
    (fun _ _ => norm_nonneg _) hratio
  exact ⟨hi,hb.trans (mul_le_mul_of_nonneg_left hki.2 hC)⟩

end
end IsingBulk.Tail
