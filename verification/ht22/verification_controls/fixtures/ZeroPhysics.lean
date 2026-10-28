import IsingBulk.HT22.Controls.Basic
-- EXPECTED REJECTION: the actual real-physics premise rejects zero correlations.
example : IsingBulk.HT22.PhysicalScope.PublishedRealHTSpinFormFactors
    (fun _ _ => 0) := by
  exact IsingBulk.HT22.Controls.zero_not_physical
