import IsingBulk.Tail.AllBranchExteriorPositiveProduct
import IsingBulk.Tail.AllBranchExteriorEqualityGeometry

/-! Finite extreme-coordinate cover, applied after taking absolute values.
No derivative of a minimum or maximum selector occurs. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

theorem allBranchExterior_oriented_extrema {N : ℕ} (u : Fin N → ℝ)
    (hu : 0 < allBranchExteriorDiameter u) :
    ∃ p q : Fin N, p ≠ q ∧ u q-u p=allBranchExteriorDiameter u ∧
      ∀ i, u p ≤ u i ∧ u i ≤ u q := by
  have hbound (p q : Fin N) (he : u q-u p=allBranchExteriorDiameter u) :
      ∀ i, u p ≤ u i ∧ u i ≤ u q := by
    intro i
    have hpi := (abs_le.mp (allBranchExterior_pair_le_diameter u p i)).1
    have hiq := (abs_le.mp (allBranchExterior_pair_le_diameter u i q)).1
    constructor <;> linarith
  obtain ⟨p,q,hpq,he⟩ := allBranchExterior_diameter_attained u hu
  by_cases horder : u p ≤ u q
  · have he' : u q-u p=allBranchExteriorDiameter u := by
      rwa [abs_of_nonpos (sub_nonpos.mpr horder),neg_sub] at he
    exact ⟨p,q,ne_of_lt hpq,he',hbound p q he'⟩
  · have he' : u p-u q=allBranchExteriorDiameter u := by
      rwa [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge horder))] at he
    exact ⟨q,p,(ne_of_lt hpq).symm,he',hbound q p he'⟩

def allBranchExteriorPositiveDiameterRegion {N : ℕ} (R a D : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun _ => 0) (fun _ => R) ∩
    {u | 0 < allBranchExteriorDiameter u ∧ allBranchExteriorDiameter u ≤ D ∧ ∃ q, a ≤ u q}

theorem allBranchExterior_positive_diameter_region_measurable {N : ℕ} (R a D : ℝ) :
    MeasurableSet (@allBranchExteriorPositiveDiameterRegion N R a D) := by
  have hm := (@allBranchExterior_diameter_continuous N).measurable
  unfold allBranchExteriorPositiveDiameterRegion
  measurability

theorem allBranchExterior_positive_diameter_region_cover {N : ℕ} {R a D : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ allBranchExteriorPositiveDiameterRegion R a D) :
    ∃ p q : Fin N, p ≠ q ∧ u ∈ allBranchExteriorPositiveGapCell p q R a D ∧
      u q-u p=allBranchExteriorDiameter u := by
  obtain ⟨p,q,hpq,he,hbounds⟩ := allBranchExterior_oriented_extrema u hu.2.1
  obtain ⟨v,hv⟩ := hu.2.2.2
  have hpos : 0 < u q-u p := he.symm ▸ hu.2.1
  exact ⟨p,q,hpq,⟨⟨hu.1,hv.trans (hbounds v).2,hpos.le⟩,hpos,he.symm ▸ hu.2.2.1⟩,he⟩

theorem allBranchExterior_positive_kernel_continuousOn {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) {ε R α β : ℝ} (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn (@allBranchExteriorPositiveKernel N d ε α β) (Icc (fun _ => 0) (fun _ => R)) := by
  have hL := allBranchExterior_arclength_continuousOn B ε R hε hεr hRB
  have hprod : ContinuousOn (fun u : Fin N → ℝ => ∏ i, ‖deriv (originalPhase d ε) (u i)‖)
      (Icc (fun _ => 0) (fun _ => R)) := by
    apply continuousOn_finsetProd
    intro i _
    exact hL.comp (continuous_apply i).continuousOn (fun u hu => ⟨by linarith [hu.1 i],hu.2 i⟩)
  have hphase : ContinuousOn (@allBranchExteriorTotalPhase N d ε) (Icc (fun _ => 0) (fun _ => R)) := by
    intro u hu
    exact (allBranchExterior_total_hasFDerivAt B ε hε hεr u
      (fun i => ⟨hu.1 i,(hu.2 i).trans hRB⟩)).continuousAt.continuousWithinAt
  exact hprod.mul ((twoPhaseKernel_continuous hα hβ).continuousOn.comp
    (((continuous_finsetSum _ (fun i _ => continuous_apply i)).sub continuous_const).continuousOn.prodMk hphase)
    (fun _ _ => mem_univ _))

end
end IsingBulk.Tail
