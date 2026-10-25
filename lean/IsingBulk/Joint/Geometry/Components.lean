import IsingBulk.Joint.Geometry.ComponentsBoundary
import IsingBulk.Joint.Geometry.SpectralComplement

namespace IsingBulk.Joint
noncomputable section
open Set

theorem component_eq_of_frontier_subset {D F : Set Coupling}
    (ho : IsOpen D) (hc : IsPreconnected D) (hs : D ⊆ Fᶜ)
    (hb : frontier D ⊆ F) {a : Coupling} (ha : a ∈ D) :
    connectedComponentIn Fᶜ a = D := by
  apply Set.Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset ho
    · exact ⟨a,mem_connectedComponentIn (hs ha),ha⟩
    · rintro K ⟨hK,hcomp⟩
      by_contra hn
      have hf : K ∈ frontier D := by rw [ho.frontier_eq]; exact ⟨hK,hn⟩
      exact (connectedComponentIn_subset Fᶜ a hcomp) (hb hf)
  · exact hc.subset_connectedComponentIn ha hs

theorem highDomain_isPreconnected : IsPreconnected highDomain := by
  let : ContractibleSpace highDomain := highDomain_contractible
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

theorem lowDomain_isPreconnected : IsPreconnected lowDomain := by
  let : ContractibleSpace lowDomain := lowDomain_contractible
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

theorem highDomain_component (a : Coupling) (ha : a ∈ highDomain) :
    connectedComponentIn spectralSetᶜ a = highDomain :=
  component_eq_of_frontier_subset highDomain_isOpen highDomain_isPreconnected
    highDomain_subset_spectralComplement frontier_high_subset_spectralSet ha

theorem lowDomain_component (a : Coupling) (ha : a ∈ lowDomain) :
    connectedComponentIn spectralSetᶜ a = lowDomain :=
  component_eq_of_frontier_subset lowDomain_isOpen lowDomain_isPreconnected
    lowDomain_subset_spectralComplement frontier_low_subset_spectralSet ha

theorem highDomain_origin_component : connectedComponentIn spectralSetᶜ 0 = highDomain :=
  highDomain_component 0 origin_mem_highDomain

end
end IsingBulk.Joint
