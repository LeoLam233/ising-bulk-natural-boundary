import IsingBulk.Joint.Transverse.FamilyArbitraryQuantitative

namespace IsingBulk.Joint
noncomputable section
open Transverse Anisotropic Set Filter Metric
open scoped Topology

/-- Every local nonramified analytic family has a constructed common analytic
normalization with both inverse identities and explicit original-family recovery.
Every compact admissible parameter subfamily has the complete quantitative
physical estimates. No exact-normalization germ is an input to these fields. -/
structure JointArbitraryPositiveFamilyConclusion : Prop where
  high : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {b : ℝ} (curve : ℂ × E→Coupling)
      {eta₀ : E} (_hc : AnalyticAt ℂ curve (0,eta₀)) (_hS₀ : S (curve (0,eta₀))≠0)
      (_hB₀ : 0<(transferB (curve (0,eta₀))).im)
      (_hzero : positiveParameter b (curve (0,eta₀))=0)
      (_hd : deriv (fun z=>positiveParameter b (curve (z,eta₀))) 0≠0)
      (_hb : |b|<1) (_hprime : b∈primePhaseCosines) ,
      ∃N : FamilyNormalization (fun q=>positiveParameter b (curve q)) eta₀,
        (∀z eta,‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
          N.normalizedFamily curve (positiveParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
        ∀Q : Set E,IsCompact Q → (∀eta∈Q,‖eta-eta₀‖<N.radius) →
        (∀eta∈Q,curve (0,eta)∈frontier highDomain) →
        (∀eta∈Q,S (curve (0,eta))≠0) → (∀eta∈Q,p (curve (0,eta))^2≠1) →
        (∀eta∈Q,0<(transferB (curve (0,eta))).im) →
        (∀eta∈Q,positiveParameter b (curve (0,eta))=0) →
        PositiveHighFamilyEstimates b (N.normalizedFamily curve) Q
  low : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {b : ℝ} (curve : ℂ × E→Coupling)
      {eta₀ : E} (_hc : AnalyticAt ℂ curve (0,eta₀)) (_hS₀ : S (curve (0,eta₀))≠0)
      (_hB₀ : 0<(transferB (curve (0,eta₀))).im)
      (_hzero : positiveParameter b (curve (0,eta₀))=0)
      (_hd : deriv (fun z=>positiveParameter b (curve (z,eta₀))) 0≠0)
      (_hb : |b|<1) (_hprime : b∈primePhaseCosines) ,
      ∃N : FamilyNormalization (fun q=>positiveParameter b (curve q)) eta₀,
        (∀z eta,‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
          N.normalizedFamily curve (positiveParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
        ∀Q : Set E,IsCompact Q → (∀eta∈Q,‖eta-eta₀‖<N.radius) →
        (∀eta∈Q,curve (0,eta)∈frontier lowDomain) →
        (∀eta∈Q,S (curve (0,eta))≠0) → (∀eta∈Q,p (curve (0,eta))^2≠1) →
        (∀eta∈Q,0<(transferB (curve (0,eta))).im) →
        (∀eta∈Q,positiveParameter b (curve (0,eta))=0) →
        PositiveLowFamilyEstimates b (N.normalizedFamily curve) Q
  negative_even_low : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {b : ℝ} (curve : ℂ × E→Coupling)
      {eta₀ : E} (_hc : AnalyticAt ℂ curve (0,eta₀)) (_hS₀ : S (curve (0,eta₀))≠0)
      (_hB₀ : 0<(-transferB (curve (0,eta₀))).im)
      (_hzero : negativeParameter b (curve (0,eta₀))=0)
      (_hd : deriv (fun z=>negativeParameter b (curve (z,eta₀))) 0≠0)
      (_hb : |b|<1) (_hprime : b∈primePhaseCosines) ,
      ∃N : FamilyNormalization (fun q=>negativeParameter b (curve q)) eta₀,
        (∀z eta,‖z‖<N.radius → ‖eta-eta₀‖<N.radius →
          N.normalizedFamily curve (negativeParameter b (curve (z,eta)),eta)=curve (z,eta)) ∧
        ∀Q : Set E,IsCompact Q → (∀eta∈Q,‖eta-eta₀‖<N.radius) →
        (∀eta∈Q,curve (0,eta)∈frontier lowDomain) →
        (∀eta∈Q,S (curve (0,eta))≠0) → (∀eta∈Q,p (curve (0,eta))^2≠1) →
        (∀eta∈Q,0<(-transferB (curve (0,eta))).im) →
        (∀eta∈Q,negativeParameter b (curve (0,eta))=0) →
        NegativeEvenLowFamilyEstimates b (N.normalizedFamily curve) Q

theorem joint_arbitrary_positive_family_conclusion : JointArbitraryPositiveFamilyConclusion where
  high := @Transverse.positive_high_arbitrary_family_quantitative
  low := @Transverse.positive_low_arbitrary_family_quantitative
  negative_even_low := @Transverse.negative_even_low_arbitrary_family_quantitative

end
end IsingBulk.Joint
