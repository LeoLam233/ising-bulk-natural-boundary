import IsingBulk.Joint.Transverse.FamilyMixedOrientation
import IsingBulk.Joint.Transverse.FamilyParticleSymmetry

namespace IsingBulk.Joint
noncomputable section
open Transverse

/-- Additional all-orientation clause for the actual full physical particle
series. All mixed Fréchet derivative maps and their summable tail envelopes
are transported on the same common polydisk, for both physical phases. -/
structure JointMixedFamilyOrientationConclusion : Prop where
  high : MixedPhysicalFamilyOrientationTransport highDomain highFullParticle
  low : MixedPhysicalFamilyOrientationTransport lowDomain lowFullParticle

/-- The actual particle identities and finite-order joint smoothness discharge
every generic symmetry premise. No mixed-tail estimate is assumed here. -/
theorem joint_mixed_family_orientation_conclusion : JointMixedFamilyOrientationConclusion where
  high := mixedPhysicalFamilyOrientationTransport_of_symmetries highDomain_isOpen
    (fun n _ hK=>highFullParticle_swap n (highDomain_subset_spectralComplement hK))
    (fun n _ hK=>highFullParticle_conjugate n hK)
    (fun j n _ hK=>highFullParticle_contDiffAt n j hK)
  low := mixedPhysicalFamilyOrientationTransport_of_symmetries lowDomain_isOpen
    (fun n _ hK=>lowFullParticle_swap n (lowDomain_subset_spectralComplement hK))
    (fun n _ hK=>lowFullParticle_conjugate n hK)
    (fun j n _ hK=>lowFullParticle_contDiffAt n j hK)

end
end IsingBulk.Joint
