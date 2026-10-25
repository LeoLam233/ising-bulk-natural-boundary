import IsingBulk.Joint.Transverse.AllOrientationAmbient
import IsingBulk.Joint.Geometry.Collars

/-! # The actual joint holomorphic natural boundaries
Prime-phase obstructions are dense in the entire boundaries, including singular
and ramified points. The local collar upgrades the conclusion to ordinary
componentwise holomorphic continuation.
-/
namespace IsingBulk.Joint
noncomputable section
open Set
variable {corrH corrL : PhysicalField.CorrelationFamily}

theorem high_no_holomorphic_full_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {K : Coupling} (hK : K∈frontier highDomain) :
    ¬HasHolomorphicFullExtension highDomain FormFactors.highNormalizedBulk K :=
  no_holomorphicFullExtension_on_closure
    (fun _ h => Transverse.prime_regular_high_no_holomorphic_extension hphys h.1 h.2)
    (frontier_high_subset_closure_primeRegularJointEdges hK)

theorem low_no_holomorphic_full_extension
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {K : Coupling} (hK : K∈frontier lowDomain) :
    ¬HasHolomorphicFullExtension lowDomain FormFactors.lowNormalizedBulk K :=
  no_holomorphicFullExtension_on_closure
    (fun _ h => Transverse.prime_regular_low_no_holomorphic_extension hphys h.1 h.2)
    (frontier_low_subset_closure_primeRegularJointEdges hK)

theorem high_holomorphic_natural_boundary
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    HolomorphicNaturalBoundaryOn highDomain FormFactors.highNormalizedBulk := by
  refine ⟨FormFactors.highNormalizedBulk_differentiableOn,?_⟩
  intro K hK he
  exact high_no_holomorphic_full_extension hphys hK
    (holomorphicFullExtension_of_component highDomain_hasLocalCollar hK he)

theorem low_holomorphic_natural_boundary
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    HolomorphicNaturalBoundaryOn lowDomain FormFactors.lowNormalizedBulk := by
  refine ⟨FormFactors.lowNormalizedBulk_differentiableOn,?_⟩
  intro K hK he
  exact low_no_holomorphic_full_extension hphys hK
    (holomorphicFullExtension_of_component lowDomain_hasLocalCollar hK he)

end
end IsingBulk.Joint
