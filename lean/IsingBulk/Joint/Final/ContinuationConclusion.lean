import IsingBulk.Joint.Final.PhysicalContinuation

namespace IsingBulk.Joint
noncomputable section

/-- Reachable unramified continuation cannot leave either physical component.
The Riemann domain and path are arbitrary; only the starting germ is fixed. -/
structure JointContinuationConclusion : Prop where
  high : ∀ (M : Type) [TopologicalSpace M] (R : UnramifiedHolomorphicDomain M)
    (m n : M) (γ : Path m n), R.projection m ∈ highDomain →
    m ∈ R.GermAgreement FormFactors.highNormalizedBulk →
    ∀ t : unitInterval, R.projection (γ t) ∈ highDomain
  low : ∀ (M : Type) [TopologicalSpace M] (R : UnramifiedHolomorphicDomain M)
    (m n : M) (γ : Path m n), R.projection m ∈ lowDomain →
    m ∈ R.GermAgreement FormFactors.lowNormalizedBulk →
    ∀ t : unitInterval, R.projection (γ t) ∈ lowDomain

theorem joint_continuation_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    JointContinuationConclusion where
  high := fun _ _ R _ _ γ hm hs => high_finite_continuation_stays hphys R γ hm hs
  low := fun _ _ R _ _ γ hm hs => low_finite_continuation_stays hphys R γ hm hs

end
end IsingBulk.Joint
