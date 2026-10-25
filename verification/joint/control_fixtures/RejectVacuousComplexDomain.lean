import IsingBulk.Joint.Controls.Nonvacuity
open IsingBulk.Joint
example : highDomain = (∅ : Set Coupling) := by
  -- EXPECT_FAILURE_HERE
  exact Controls.physical_domains_nonempty.1
