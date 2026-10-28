import IsingBulk.HT22.Controls.Basic
-- EXPECTED REJECTION: origin-deleted correlations cannot fill the physical premise.
example (corr : ℝ → IsingBulk.HT22.PhysicalScope.LatticeSite → ℝ) :
    IsingBulk.HT22.PhysicalScope.PublishedRealHTSpinFormFactors
      (fun s v => if v=(0,0) then 0 else corr s v) := by
  exact IsingBulk.HT22.Controls.omitted_origin_not_physical corr
