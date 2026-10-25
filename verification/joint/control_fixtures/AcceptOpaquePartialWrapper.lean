import JointAudit
namespace IsingBulk.JointControl
partial def looping (n : Nat) : Nat := looping (n+1)
/-- The safe opaque wrapper has a logical default value. This reflexive theorem
does not assert termination or the execution semantics of the partial helper. -/
theorem opaqueEndpoint (n : Nat) : looping n = looping n := rfl
end IsingBulk.JointControl
run_cmd JointAudit.scanActualClosure #[`IsingBulk.JointControl.opaqueEndpoint]
