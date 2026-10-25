import JointAudit
namespace IsingBulk.JointControl
theorem safe : True := True.intro
theorem unused : 1 = 1 := rfl
end IsingBulk.JointControl
-- EXPECT_FAILURE_HERE
run_cmd JointAudit.scanActualClosure #[`IsingBulk.JointControl.safe] #[`IsingBulk.JointControl.unused]
