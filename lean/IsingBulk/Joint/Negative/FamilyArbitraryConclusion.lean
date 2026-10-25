import IsingBulk.Joint.Negative.FamilyArbitraryPhysical

namespace IsingBulk.Joint
noncomputable section
open Set Metric Transverse

/-- The arbitrary-family negative-odd clause starts from a nonramified
ORIGINAL family. A common analytic inverse and its exact recovery are results.
Every compact admissible subfamily in that disk receives the true complete
coefficient obstruction, literal physical boundary jets, and all mixed tails. -/
structure JointArbitraryNegativeFamilyConclusion : Prop where
  negative_high : ∀(E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {b : ℝ} (curve : ℂ × E→Coupling) {eta₀ : E},
    AnalyticAt ℂ curve (0,eta₀) → S (curve (0,eta₀))≠0 →
    (transferB (curve (0,eta₀))).im<0 → b∈Anisotropic.primePhaseCosines →
    Negative.edgeParameter b (curve (0,eta₀))=0 →
    deriv (fun z=>Negative.edgeParameter b (curve (z,eta₀))) 0≠0 →
    ∃N : FamilyNormalization (fun q=>Negative.edgeParameter b (curve q)) eta₀,
      (∀z eta, ‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
        N.normalizedFamily curve (Negative.edgeParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
      ∀Q : Set E, IsCompact Q → Q⊆ball eta₀ N.radius →
        (∀eta∈Q,Negative.edgeParameter b (curve (0,eta))=0) →
        (∀eta∈Q,curve (0,eta)∈frontier highDomain) →
        (∀eta∈Q,S (curve (0,eta))≠0) →
        (∀eta∈Q,p (curve (0,eta))^2≠1) →
        (∀eta∈Q,(transferB (curve (0,eta))).im<0) →
        NegativeHighFamilyEstimates (N.normalizedFamily curve) Q

theorem joint_arbitrary_negative_family_conclusion : JointArbitraryNegativeFamilyConclusion where
  negative_high := @Negative.arbitrary_negative_high_family_estimates

end
end IsingBulk.Joint
