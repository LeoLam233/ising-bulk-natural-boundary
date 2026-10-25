import JointAudit
namespace IsingBulk.JointControl
partial def looping (n : Nat) : Nat := looping (n+1)
-- EXPECT_FAILURE_HERE
theorem partialEndpoint (n : Nat) : looping._unsafe_rec n = looping._unsafe_rec n := rfl
end IsingBulk.JointControl
