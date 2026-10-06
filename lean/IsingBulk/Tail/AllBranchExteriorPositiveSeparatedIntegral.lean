import IsingBulk.Tail.AllBranchExteriorPositiveDiameterIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory Filter
open scoped BigOperators

/-- The separated positive region uses the same extreme-pair integral with
one diameter power, divided by the fixed lower separation. -/
theorem allBranchExterior_positive_separated_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a D R σ α β : ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hD : 0 < D) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    let S := @allBranchExteriorPositiveDiameterRegion N R a D ∩ {u | σ ≤ allBranchExteriorDiameter u}
    IntegrableOn (allBranchExteriorPositiveKernel d ε α β) S ∧
    (∫ u in S, allBranchExteriorPositiveKernel d ε α β u) ≤
      σ⁻¹*((N:ℝ)^2*((D*allBranchExteriorPositiveCost B a D)*
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2)))) := by
  dsimp only
  let S := @allBranchExteriorPositiveDiameterRegion N R a D ∩ {u | σ ≤ allBranchExteriorDiameter u}
  let T := @allBranchExteriorPositiveDiameterRegion N R a D
  let K := @allBranchExteriorPositiveKernel N d ε α β
  have hT := allBranchExterior_positive_diameter_region_measurable (N := N) R a D
  have hS : MeasurableSet S := hT.inter (measurableSet_le measurable_const
    (@allBranchExterior_diameter_continuous N).measurable)
  have hpow := allBranchExterior_positive_diameter_integral (N := N) B ε a D R α β 0
    hε hεr ha hD hsmall₁ hsmall₂ hR hRB hRπ hα hα1 hβ hβ1
  simp only [zero_add,pow_one] at hpow
  have hKi : IntegrableOn K S :=
    (allBranchExterior_positive_kernel_continuousOn B hε hεr hR hRB hα hβ).integrableOn_compact
      isCompact_Icc |>.mono_set (fun _ hu => hu.1.1)
  have hnonneg (u : Fin N → ℝ) : 0 ≤ allBranchExteriorDiameter u*K u :=
    mul_nonneg (allBranchExterior_diameter_nonneg u) (allBranchExterior_positive_kernel_nonneg d ε α β u)
  have hpoint (u : Fin N → ℝ) (hu : u ∈ S) : K u ≤ σ⁻¹*(allBranchExteriorDiameter u*K u) := by
    have hh := mul_le_mul_of_nonneg_right hu.2 (allBranchExterior_positive_kernel_nonneg d ε α β u)
    calc
      K u = σ⁻¹*(σ*K u) := by rw [← mul_assoc,inv_mul_cancel₀ hσ.ne',one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hσ.le)
  refine ⟨hKi,?_⟩
  calc
    _ ≤ ∫ u in S, σ⁻¹*(allBranchExteriorDiameter u*K u) :=
      setIntegral_mono_on hKi ((hpow.1.mono_set inter_subset_left).const_mul σ⁻¹) hS hpoint
    _ = σ⁻¹*(∫ u in S, allBranchExteriorDiameter u*K u) := integral_const_mul _ _
    _ ≤ σ⁻¹*(∫ u in T, allBranchExteriorDiameter u*K u) := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hpow.1 (Eventually.of_forall hnonneg)
        (Eventually.of_forall (show S ⊆ T from inter_subset_left))) (inv_nonneg.mpr hσ.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow.2 (inv_nonneg.mpr hσ.le)

end
end IsingBulk.Tail
