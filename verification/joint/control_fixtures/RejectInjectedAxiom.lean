import JointAudit
namespace IsingBulk.JointControl
axiom counterfeit : False
theorem falseEndpoint : False := counterfeit
end IsingBulk.JointControl
-- EXPECT_FAILURE_HERE
run_cmd JointAudit.scanActualClosure #[`IsingBulk.JointControl.falseEndpoint]
