import IsingBulk.Joint.Final.CoreConclusion
import IsingBulk.Joint.Final.PositiveFamilyConclusion
import IsingBulk.Joint.Final.NegativeFamilyConclusion
import IsingBulk.Joint.Final.RatioFamilyConclusion
import IsingBulk.Joint.Negative.FamilyMixedConclusion
import IsingBulk.Joint.Transverse.FamilyOrientationConclusion
import IsingBulk.Joint.Transverse.FamilyNormalizationConclusion
import IsingBulk.Joint.Transverse.FamilyMixedOrientationConclusion
import IsingBulk.Joint.Transverse.FamilyArbitraryConclusion
import IsingBulk.Joint.Negative.FamilyArbitraryConclusion
import IsingBulk.Joint.Geometry.FaceDensityConclusion

/-! The single delivery endpoint. Every mathematical field is proved internally;
the only explicit inputs are the common classical real spin and Gibbs-field
families. Kernel compilation of this assembly is not a validation receipt. -/
namespace IsingBulk.Joint
noncomputable section

structure JointFullConclusion (corrH corrL : PhysicalField.CorrelationFamily)
    (mH mL : PhysicalField.MagnetizationFamily) : Prop where
  core : JointCoreConclusion corrH corrL mH mL
  positive_families : JointPositiveFamilyConclusion
  negative_families : JointNegativeFamilyConclusion
  negative_mixed_families : JointNegativeMixedFamilyConclusion
  actual_ratio_families : JointRatioFamilyConclusion
  family_orientations : JointFamilyOrientationConclusion
  mixed_family_orientations : JointMixedFamilyOrientationConclusion
  family_normalization : JointFamilyNormalizationConclusion
  arbitrary_positive_families : JointArbitraryPositiveFamilyConclusion
  arbitrary_negative_families : JointArbitraryNegativeFamilyConclusion
  regular_face_density : JointFaceDensityConclusion

theorem full_joint_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    {mH mL : PhysicalField.MagnetizationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    (hfields : PhysicalField.PublishedRealGibbsFamily corrH corrL mH mL) :
    JointFullConclusion corrH corrL mH mL where
  core := joint_core_conclusion hphys hfields
  positive_families := joint_positive_family_conclusion
  negative_families := joint_negative_family_conclusion
  negative_mixed_families := joint_negative_mixed_family_conclusion
  actual_ratio_families := joint_ratio_family_conclusion
  family_orientations := joint_family_orientation_conclusion hphys
  mixed_family_orientations := joint_mixed_family_orientation_conclusion
  family_normalization := joint_family_normalization_conclusion
  arbitrary_positive_families := joint_arbitrary_positive_family_conclusion
  arbitrary_negative_families := joint_arbitrary_negative_family_conclusion
  regular_face_density := joint_face_density_conclusion

end
end IsingBulk.Joint
