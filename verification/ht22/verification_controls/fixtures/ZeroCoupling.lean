import IsingBulk.HT22.Controls.Scope
-- EXPECTED REJECTION: J=0 is a proved extension countermodel to removing J>0.
example : ¬IsingBulk.HT.Final.HasInteriorExtension
    (IsingBulk.HT22.Physical.physicalSusceptibility 0) 1 := by
  exact IsingBulk.HT22.Controls.zero_coupling_extends 1
