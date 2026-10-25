import IsingBulk.Joint.Final.FullConclusion
open IsingBulk.Joint
example {corrH corrL : PhysicalField.CorrelationFamily}
    {mH mL : PhysicalField.MagnetizationFamily}
    (hcore : JointCoreConclusion corrH corrL mH mL) :
    JointFullConclusion corrH corrL mH mL :=
  -- EXPECT_FAILURE_HERE
  hcore
