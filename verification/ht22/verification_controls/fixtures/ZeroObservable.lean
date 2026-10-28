import IsingBulk.HT22.Controls.Basic
-- EXPECTED REJECTION: an entire zero observable cannot replace the natural-boundary target.
example : ∀ z : ℂ, ‖z‖=1 →
    ¬IsingBulk.HT.Final.HasInteriorExtension (fun _ : ℂ => 0) z := by
  exact IsingBulk.HT22.Controls.zero_not_natural_boundary
