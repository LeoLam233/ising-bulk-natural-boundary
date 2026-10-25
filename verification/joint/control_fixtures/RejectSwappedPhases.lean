import IsingBulk.Joint.Final.IsotropicConclusion
open IsingBulk.Joint
example {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {z : ℂ} (hz : z ∈ IsingBulk.Anisotropic.omegaH 1) :
    FormFactors.highNormalizedBulk (ratioSlice 1 z) =
      IsingBulk.Tail.exteriorNormalizedBulk (Complex.sinh z) :=
  -- EXPECT_FAILURE_HERE
  (joint_isotropic_conclusion hphys).high_descent z hz
