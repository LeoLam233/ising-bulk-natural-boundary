import IsingBulk.HT.Lie.SignedNearKernelMajorant
import IsingBulk.Tail.AllBranchExteriorNearKernelMajorant

namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Tail IsingBulk.Branch IsingBulk.Lie Set MeasureTheory

/-- The same integrable kernel majorant controls the far chart, including
mixed coordinate signs. The one extra inverse separation is explicit. -/
theorem signed_far_kernel_majorant_dominates {N : ℕ} (phase : ℂ) (d : LocalBranchData)
    (ε R a D σ : ℝ) (hσ : 0 < σ) (v : Fin N) (u : Fin N → ℝ)
    (hu : ∀ i, |u i| ≤ R) (hanchor : a ≤ |u v|)
    (hsep : σ ≤ allBranchExteriorDiameter u) (hD : allBranchExteriorDiameter u ≤ D) :
    signedExteriorKernelDensity phase d ε u ≤ σ⁻¹*signedExteriorNearKernelMajorant phase d ε R a D v 1 u := by
  classical
  have hdiam : 0 < allBranchExteriorDiameter u := hσ.trans_le hsep
  have hD0 : 0 ≤ D := hdiam.le.trans hD
  have hp : 0 ≤ (allBranchExteriorPositiveDiameterRegion R a D).indicator
      (fun x => allBranchExteriorDiameter x^1*signedExteriorKernelDensity phase d ε x) u :=
    indicator_nonneg (fun x _ => mul_nonneg (pow_nonneg (allBranchExterior_diameter_nonneg x) 1)
      (signed_kernel_density_nonneg phase d ε x)) u
  have hn : 0 ≤ (allBranchExteriorNegativeRegion v R a).indicator (signedExteriorKernelDensity phase d ε) u :=
    indicator_nonneg (fun x _ => signed_kernel_density_nonneg phase d ε x) u
  have hbound : σ*signedExteriorKernelDensity phase d ε u ≤ signedExteriorNearKernelMajorant phase d ε R a D v 1 u := by
    unfold signedExteriorNearKernelMajorant
    by_cases hsign : ∀ i, 0 ≤ u i
    · have hv : a ≤ u v := by simpa only [abs_of_nonneg (hsign v)] using hanchor
      have hm : u ∈ allBranchExteriorPositiveDiameterRegion R a D :=
        ⟨⟨hsign,fun i => (abs_le.mp (hu i)).2⟩,hdiam,hD,v,hv⟩
      rw [indicator_of_mem hm,pow_one,pow_one]
      exact (mul_le_mul_of_nonneg_right hsep (signed_kernel_density_nonneg phase d ε u)).trans
        (le_add_of_nonneg_right (mul_nonneg hD0 hn))
    · push Not at hsign
      obtain ⟨i,hi⟩ := hsign
      have hm : u ∈ allBranchExteriorNegativeRegion v R a :=
        ⟨⟨fun k => (abs_le.mp (hu k)).1,fun k => (abs_le.mp (hu k)).2⟩,hanchor,i,hi.le⟩
      rw [indicator_of_mem hm,pow_one]
      exact (mul_le_mul_of_nonneg_right (hsep.trans hD) (signed_kernel_density_nonneg phase d ε u)).trans
        (le_add_of_nonneg_left hp)
  calc
    _ = σ⁻¹*(σ*signedExteriorKernelDensity phase d ε u) := by rw [← mul_assoc,inv_mul_cancel₀ hσ.ne',one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hσ.le)

end
end IsingBulk.HT.Lie
