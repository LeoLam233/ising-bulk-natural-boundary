import JointAudit
namespace IsingBulk.JointControl
partial def unusedExecutable (n : Nat) : Nat := unusedExecutable (n+1)
theorem safe : True := True.intro
end IsingBulk.JointControl
run_cmd JointAudit.scanActualClosure #[`IsingBulk.JointControl.safe]
