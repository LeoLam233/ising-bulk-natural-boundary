import IsingBulk.Joint.Controls.IndependentScope
import IsingBulk.Joint.Isotropic.BoundaryPreimages
import IsingBulk.Joint.Slices.EdgeTransfer

namespace IsingBulk.Joint.Controls
noncomputable section
open Set

/-- The actual high-temperature boundary and the selected regular prime set
are nonempty. The obstruction quantifiers are not vacuous domain predicates. -/
theorem high_selected_edges_nonempty :
    (frontier highDomain ∩ primeRegularJointEdges).Nonempty :=
  Set.Nonempty.of_closure
    ⟨_,frontier_high_subset_closure_primeRegularJointEdges decoupled_tip_mem_frontier⟩

theorem low_frontier_nonempty : (frontier lowDomain).Nonempty := by
  obtain ⟨z,hz,_⟩ := unit_preimage_low 1 (by norm_num)
  exact ⟨ratioSlice 1 z,ratioSlice_low_frontier (by norm_num) hz⟩

theorem low_selected_edges_nonempty :
    (frontier lowDomain ∩ primeRegularJointEdges).Nonempty := by
  obtain ⟨K,hK⟩ := low_frontier_nonempty
  exact Set.Nonempty.of_closure
    ⟨K,frontier_low_subset_closure_primeRegularJointEdges hK⟩

/-- Both full domains have actual points; low contains the positive-real
supercritical center, while high contains a genuine independent complex point. -/
theorem physical_domains_nonempty : highDomain.Nonempty ∧ lowDomain.Nonempty :=
  ⟨⟨0,zero_mem_highDomain⟩,⟨lowCenter.val,lowCenter.property⟩⟩

end
end IsingBulk.Joint.Controls
