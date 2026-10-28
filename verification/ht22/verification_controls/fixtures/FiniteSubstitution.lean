import IsingBulk.HT22.Controls.FiniteTruncation
-- EXPECTED REJECTION: every fixed finite physical odd prefix differs from the full source.
example (m : ℕ) : Set.EqOn IsingBulk.HT22.Physical.oddSeries
    (IsingBulk.HT22.Controls.finiteOddPrefix m) {t : ℂ | 1<‖t‖} := by
  exact IsingBulk.HT22.Controls.finiteOddPrefix_not_full m
