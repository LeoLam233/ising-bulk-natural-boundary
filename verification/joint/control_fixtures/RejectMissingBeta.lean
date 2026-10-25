import IsingBulk.Joint.Final.PhysicalConclusion
open IsingBulk.Joint IsingBulk.Joint.PhysicalField
example {corrH corrL : CorrelationFamily} {mH mL : MagnetizationFamily}
    (hphys : PublishedRealSpinFamily corrH corrL)
    (hfields : PublishedRealGibbsFamily corrH corrL mH mL)
    {J lam x : ℝ} (hJ : 0 < J) (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct (realSlice lam x) < 1) :
    HasDerivAt (mH J (lam*J) (x/(2*J))) (highCovarianceSum corrH (realSlice lam x)) 0 :=
  -- EXPECT_FAILURE_HERE
  (high_energy_field_derivative hphys hfields hJ hlam hx hp).1
