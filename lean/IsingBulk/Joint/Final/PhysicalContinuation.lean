import IsingBulk.Joint.Final.ContinuationPath
import IsingBulk.Joint.Final.JointBoundary

namespace IsingBulk.Joint
noncomputable section
open Set

/-- Every finite continuation path from the actual high-temperature germ in an
unramified Riemann domain stays over its physical joint component. -/
theorem high_finite_continuation_stays
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {M : Type*} [TopologicalSpace M] (R : UnramifiedHolomorphicDomain M)
    {m n : M} (γ : Path m n) (hm : R.projection m ∈ highDomain)
    (hstart : m ∈ R.GermAgreement FormFactors.highNormalizedBulk) :
    ∀ t : unitInterval, R.projection (γ t) ∈ highDomain :=
  R.finite_path_stays_in_domain highDomain_isOpen
    (high_holomorphic_natural_boundary hphys) γ hm hstart

/-- The analogous assertion for the low-temperature pure-phase connected germ.
Only the starting germ is specified; agreement along the path is proved. -/
theorem low_finite_continuation_stays
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {M : Type*} [TopologicalSpace M] (R : UnramifiedHolomorphicDomain M)
    {m n : M} (γ : Path m n) (hm : R.projection m ∈ lowDomain)
    (hstart : m ∈ R.GermAgreement FormFactors.lowNormalizedBulk) :
    ∀ t : unitInterval, R.projection (γ t) ∈ lowDomain :=
  R.finite_path_stays_in_domain lowDomain_isOpen
    (low_holomorphic_natural_boundary hphys) γ hm hstart

end
end IsingBulk.Joint
