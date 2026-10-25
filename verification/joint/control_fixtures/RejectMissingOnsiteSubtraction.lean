import IsingBulk.Joint.Final.PhysicalConclusion
open IsingBulk.Joint IsingBulk.Joint.PhysicalField
example {corrH corrL : CorrelationFamily}
    (hphys : PublishedRealSpinFamily corrH corrL)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hp : 1 < realProduct (x,y)) :
    corrL (x,y) (0,0)-magnetizationSq (x,y) = 1 :=
  -- EXPECT_FAILURE_HERE
  low_connected_onsite hphys hx hy hp
