import IsingBulk.Joint.Final.GeometryConclusion
import IsingBulk.Joint.Final.NormalConclusion
import IsingBulk.Joint.Final.BoundaryConclusion
import IsingBulk.Joint.Final.RecoveryConclusion
import IsingBulk.Joint.Final.IsotropicConclusion
import IsingBulk.Joint.Final.ContinuationConclusion
import IsingBulk.Joint.Final.PhysicalConclusion

/-! This is the qualitative core, not the full J AND R AND I delivery endpoint.
The mandated quantitative compact-family uniformity is a separate additional
clause and must be attached by the final endpoint before candidate freezing. -/
namespace IsingBulk.Joint
noncomputable section

structure JointCoreConclusion (corrH corrL : PhysicalField.CorrelationFamily)
    (mH mL : PhysicalField.MagnetizationFamily) : Prop where
  geometry : JointGeometryConclusion
  normal : JointNormalConclusion
  boundary : JointBoundaryConclusion
  recovery : JointRecoveryConclusion
  isotropic : JointIsotropicConclusion
  continuation : JointContinuationConclusion
  physical : JointPhysicalConclusion corrH corrL mH mL

theorem joint_core_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    {mH mL : PhysicalField.MagnetizationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    (hfields : PhysicalField.PublishedRealGibbsFamily corrH corrL mH mL) :
    JointCoreConclusion corrH corrL mH mL where
  geometry := joint_geometry_conclusion
  normal := joint_normal_conclusion
  boundary := joint_boundary_conclusion hphys
  recovery := joint_recovery_conclusion hphys
  isotropic := joint_isotropic_conclusion hphys
  continuation := joint_continuation_conclusion hphys
  physical := joint_physical_conclusion hphys hfields

end
end IsingBulk.Joint
