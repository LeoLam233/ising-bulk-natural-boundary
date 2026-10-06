import IsingBulk.Tail.MicrocoreProductLaplace
import IsingBulk.Tail.MicrocoreBranchLaplace
import Mathlib.Topology.Order.ProjIcc

/-! Product arclength estimate on the actual original branch curves. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch MeasureTheory Set
open scoped BigOperators

 theorem original_branch_product_laplace_bound (d : LocalBranchData) :
    ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ ∀ (n : ℕ) (ε b : ℝ),
      0 < ε → ε < r → 0 < b → b < r →
      let μ := Measure.pi (fun _ : Fin (n+2) => volume.restrict (Icc (-b) b))
      Integrable (fun u : Fin (n+2) → ℝ =>
        (∏ i, ‖deriv (originalPhase d ε) (u i)‖)/(∑ i, ‖originalPhase d ε (u i)‖)) μ ∧
      (∫ u : Fin (n+2) → ℝ,
        (∏ i, ‖deriv (originalPhase d ε) (u i)‖)/(∑ i, ‖originalPhase d ε (u i)‖) ∂μ) ≤
        2*K^(n+2)*(Real.sqrt b)^(n+1) := by
  obtain ⟨K,rL,hK,hrL,hL⟩ := original_branch_laplace_bound d
  obtain ⟨rB,hrB,hB⟩ := original_branch_inclusion d
  let r := min rL rB
  refine ⟨K,r,hK,lt_min hrL hrB,?_⟩
  intro n ε b hε hεr hb hbr
  dsimp only
  have hεL : ε < rL := hεr.trans_le (min_le_left _ _)
  have hbL : b < rL := hbr.trans_le (min_le_left _ _)
  have hεB : ε < rB := hεr.trans_le (min_le_right _ _)
  have hbB : b < rB := hbr.trans_le (min_le_right _ _)
  have hab : -b ≤ b := by linarith
  let p : ℝ → Icc (-b) b := projIcc (-b) b hab
  let a : ℝ → ℝ := fun u => ‖originalPhase d ε (p u)‖
  let f : ℝ → ℝ := fun u => ‖deriv (originalPhase d ε) (p u)‖
  have hphase : ContinuousOn (originalPhase d ε) (Icc (-b) b) := by
    intro u hu
    obtain ⟨hre,him⟩ := hB ε u hε hεB ((abs_le.mpr hu).trans_lt hbB)
    exact (currentPhase_hasDerivAt d ε 0 u hre him).continuousAt.continuousWithinAt
  have hderiv : ContinuousOn (deriv (originalPhase d ε)) (Icc (-b) b) := by
    intro u hu
    obtain ⟨hre,him⟩ := hB ε u hε hεB ((abs_le.mpr hu).trans_lt hbB)
    exact (currentPhase_second_hasDerivAt d ε 0 u hre him).continuousAt.continuousWithinAt
  have ha : Continuous a := hphase.domRestrict.norm.comp continuous_projIcc
  have hf : Continuous f := hderiv.domRestrict.norm.comp continuous_projIcc
  have haPos : ∀ u, 0 < a u := by
    intro u
    obtain ⟨hre,him⟩ := hB ε (p u) hε hεB ((abs_le.mpr (p u).property).trans_lt hbB)
    have hs := lowerArccos_sheet _ hre him
    apply norm_pos_iff.mpr
    intro hz
    have he : (originalPhase d ε (p u)).re = 0 := by rw [hz]; simp
    exact (ne_of_gt hs.2.1) he
  have heq : ∀ u ∈ Icc (-b) b,
      a u=‖originalPhase d ε u‖ ∧ f u=‖deriv (originalPhase d ε) u‖ := by
    intro u hu
    simp [a,f,p,projIcc_of_mem hab hu]
  have hbody : ∀ t : ℝ, 0 < t →
      Integrable (fun u => Real.exp (-t*a u)*f u) (volume.restrict (Icc (-b) b)) ∧
      (∫ u in Icc (-b) b, Real.exp (-t*a u)*f u) ≤ K*min (Real.sqrt b) t⁻¹ := by
    intro t ht
    obtain ⟨hi,hle⟩ := hL ε b t hε hεL hb hbL ht
    have hae : (fun u => Real.exp (-t*a u)*f u) =ᵐ[volume.restrict (Icc (-b) b)]
        branchCurveLaplace d ε t := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      simp only [(heq u hu).1,(heq u hu).2,branchCurveLaplace]
    constructor
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi |>.congr hae.symm
    · rw [integral_congr_ae hae,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
      exact hle
  obtain ⟨hi,hle⟩ := laplace_product_kernel_power_bound n (volume.restrict (Icc (-b) b))
    a f ha hf haPos (fun _ => norm_nonneg _) K (Real.sqrt b) hK.le (Real.sqrt_pos.mpr hb) hbody
  have hae : (fun u : Fin (n+2) → ℝ => (∏ i, f (u i))/(∑ i, a (u i))) =ᵐ[
      Measure.pi (fun _ : Fin (n+2) => volume.restrict (Icc (-b) b))]
      (fun u => (∏ i, ‖deriv (originalPhase d ε) (u i)‖)/(∑ i, ‖originalPhase d ε (u i)‖)) := by
    have hh : ∀ i : Fin (n+2), ∀ᵐ u ∂Measure.pi (fun _ : Fin (n+2) => volume.restrict (Icc (-b) b)),
        u i ∈ Icc (-b) b := fun i =>
      (Measure.tendsto_eval_ae_ae (i := i)) (ae_restrict_mem measurableSet_Icc)
    filter_upwards [ae_all_iff.mpr hh] with u hu
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => (heq (u i) (hu i)).2)
    · exact Finset.sum_congr rfl (fun i _ => (heq (u i) (hu i)).1)
  exact ⟨hi.congr hae, (integral_congr_ae hae).symm ▸ hle⟩

end
end IsingBulk.Tail
