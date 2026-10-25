import IsingBulk.Joint.Final.PhysicalConclusion
open IsingBulk.Joint IsingBulk.Joint.PhysicalField
example {corrH corrL : CorrelationFamily} {mH mL : MagnetizationFamily} :
    JointPhysicalConclusion corrH corrL mH mL :=
  -- EXPECT_FAILURE_HERE
  joint_physical_conclusion
