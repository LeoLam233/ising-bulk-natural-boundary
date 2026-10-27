import IsingBulk.Preferred22
import RootWalker
set_option pp.all true
set_option pp.universes true
set_option pp.proofs true
set_option pp.explicit true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
#print IsingBulk.Preferred22.preferred_full_target
#print IsingBulk.Preferred22.PreferredFullTarget
#print IsingBulk.Preferred22.PublishedPhysicalInputs
#print IsingBulk.Preferred22.PalmerTracyInput
#print IsingBulk.Preferred22.YangInput
#print IsingBulk.Preferred22.PreferredLatticeFubiniStatement
#print IsingBulk.Preferred22.PreferredSelectedAnalyticObligations
#print IsingBulk.Preferred22.PreferredAbsoluteTailStatement
#print IsingBulk.Preferred22.PreferredFirstSingularityStatement
#print IsingBulk.Preferred22.HasPhysicalBoundaryExtension
#print axioms IsingBulk.Preferred22.preferred_full_target
#print axioms IsingBulk.Preferred22.preferred_actual_absolute_tail
#print axioms IsingBulk.Preferred22.preferred_actual_first_singularity
audit_graph IsingBulk.Preferred22.preferred_full_target to "root"

-- Integration acceptance: exact no-premise type, checked by elaboration.
example : @IsingBulk.Preferred22.preferred_full_target = (show IsingBulk.Preferred22.PreferredFullTarget from IsingBulk.Preferred22.preferred_full_target) := rfl
