import IsingBulk.Joint.Isotropic.BoundaryPreimages
import IsingBulk.Joint.Isotropic.PhysicalDescent
import IsingBulk.Joint.Slices.FullBoundary
import IsingBulk.Joint.FormFactors.AxisRemovability

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

/-- Every unit-circle obstruction is derived by composition from the proved R
slice theorem, including ramified values ±i. No local inverse is assumed there. -/
theorem high_descendant_no_extension_from_R
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {s : ℂ} (hs : ‖s‖ = 1) :
    ¬ HasDomainExtension {w : ℂ | ‖w‖ < 1} IsingBulk.HT.Final.interiorFullBulk s := by
  obtain ⟨z,hz,hzs⟩ := unit_preimage_high s hs
  have hno := (joint_high_slice_naturalBoundary hphys (by norm_num : (0:ℝ)<1)).2 z hz
  rintro ⟨U,hU,hsU,g,hg,hgf⟩
  apply hno
  refine ⟨Complex.sinh ⁻¹' U,hU.preimage Complex.continuous_sinh,?_,g ∘ Complex.sinh,?_,?_⟩
  · change Complex.sinh z ∈ U
    rwa [hzs]
  · intro w hw
    exact (hg _ hw).comp Complex.analyticAt_sinh
  · intro w hw
    exact (hgf ⟨hw.1,((mem_omegaH_one_iff w).mp hw.2).2⟩).trans
      (joint_high_isotropic_identity hw.2).symm

theorem low_descendant_no_extension_from_R
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {s : ℂ} (hs : ‖s‖ = 1) :
    ¬ HasDomainExtension {w : ℂ | 1 < ‖w‖} IsingBulk.Tail.exteriorNormalizedBulk s := by
  obtain ⟨z,hz,hzs⟩ := unit_preimage_low s hs
  have hno := (joint_low_slice_naturalBoundary hphys (by norm_num : (0:ℝ)<1)).2 z hz
  rintro ⟨U,hU,hsU,g,hg,hgf⟩
  apply hno
  refine ⟨Complex.sinh ⁻¹' U,hU.preimage Complex.continuous_sinh,?_,g ∘ Complex.sinh,?_,?_⟩
  · change Complex.sinh z ∈ U
    rwa [hzs]
  · intro w hw
    exact (hg _ hw).comp Complex.analyticAt_sinh
  · intro w hw
    exact (hgf ⟨hw.1,((mem_omegaL_one_iff w).mp hw.2).2⟩).trans
      (joint_low_isotropic_identity (hphys 1 (by norm_num)) hw.2).symm

theorem high_descendant_zero : IsingBulk.HT.Final.interiorFullBulk 0 = 1 := by
  have h := high_descendant_on_disk (s:=0) (by norm_num)
  have hz : IsingBulk.Final.arsinhRight 0 = 0 := by simp [IsingBulk.Final.arsinhRight]
  rw [hz] at h
  simpa [ratioSlice] using h.symm

end
end IsingBulk.Joint
