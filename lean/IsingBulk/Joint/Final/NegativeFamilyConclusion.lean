import IsingBulk.Joint.Negative.FamilyRatioObstruction
import IsingBulk.Joint.Negative.FamilyRatioPhysicalConclusion

namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric
open scoped Topology

/-- The negative-odd quantitative clause is for actual complete coefficients.
All pole, normal-form, residue, cycle, beta, winding and index estimates have
been discharged internally; none is retained as a field hypothesis. -/
structure JointNegativeFamilyConclusion : Prop where
  general : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : Set E) (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) (b : ℝ),
    IsCompact Q →
    (∀ eta∈Q, AnalyticAt ℂ curve (0,eta)) →
    (∀ eta∈Q, AnalyticAt ℂ amp (0,eta)) →
    (∀ eta∈Q, S (curve (0,eta))≠0) →
    (∀ eta∈Q, (transferB (curve (0,eta))).im<0) →
    b∈Anisotropic.primePhaseCosines →
    (∀ eta∈Q, ∀ᶠ t : ℂ in 𝓝 0,
      transferC (curve (t,eta))+transferB (curve (t,eta))=
        (b:ℂ)+transferB (curve (t,eta))*t) →
    (∀ eta∈Q, ∀ᶠ t : ℂ in 𝓝 0, amp (t,eta)^2=p (curve (t,eta))) →
    Negative.CompactNegativeCoefficientObstruction curve amp Q
  physical : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : Set E) (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) (b : ℝ),
    IsCompact Q →
    (∀ eta∈Q, AnalyticAt ℂ curve (0,eta)) →
    (∀ eta∈Q, AnalyticAt ℂ amp (0,eta)) →
    (∀ eta∈Q, S (curve (0,eta))≠0) →
    (∀ eta∈Q, (transferB (curve (0,eta))).im<0) →
    (∀ eta∈Q, curve (0,eta)∈frontier highDomain) →
    (∀ eta∈Q, p (curve (0,eta))^2≠1) →
    b∈Anisotropic.primePhaseCosines →
    (∀ eta∈Q, ∀ᶠ t : ℂ in 𝓝 0,
      transferC (curve (t,eta))+transferB (curve (t,eta))=
        (b:ℂ)+transferB (curve (t,eta))*t) →
    (∀ eta∈Q, ∀ᶠ t : ℂ in 𝓝 0, amp (t,eta)^2=p (curve (t,eta))) →
    Negative.CompactNegativePhysicalObstruction curve amp Q
  actual_ratio : ∀ (b : ℝ) (z₀ lam₀ : ℂ),
    (z₀,lam₀*z₀)∈closure highDomain → p (z₀,lam₀*z₀)^2≠1 →
    S (z₀,lam₀*z₀)≠0 → (transferB (z₀,lam₀*z₀)).im<0 →
    b∈Anisotropic.primePhaseCosines →
    Negative.edgeParameter (b:ℂ) (z₀,lam₀*z₀)=0 →
    deriv (fun z=>Negative.edgeParameter (b:ℂ) (z,lam₀*z)) z₀≠0 →
    ∃ F : FormFactors.ComplexRatioFamily (Negative.edgeParameter (b:ℂ))
      FormFactors.highPrefactor (-1) z₀ lam₀,
      Negative.CompactNegativeCoefficientObstruction F.coupling
        (Negative.NegativeRatioFamily.particleAmplitude F) (closedBall lam₀ F.radius)
  actual_physical_ratio : ∀ (b : ℝ) (z₀ lam₀ : ℂ),
    (z₀,lam₀*z₀)∈closure highDomain → p (z₀,lam₀*z₀)^2≠1 →
    S (z₀,lam₀*z₀)≠0 → (transferB (z₀,lam₀*z₀)).im<0 →
    b∈Anisotropic.primePhaseCosines →
    Negative.edgeParameter (b:ℂ) (z₀,lam₀*z₀)=0 →
    deriv (fun z=>Negative.edgeParameter (b:ℂ) (z,lam₀*z)) z₀≠0 →
    ∃ F : FormFactors.ComplexRatioFamily (Negative.edgeParameter (b:ℂ))
      FormFactors.highPrefactor (-1) z₀ lam₀,
      ∃ ρ : ℝ, 0<ρ ∧ ρ≤F.radius ∧
        (∀ lam∈closedBall lam₀ ρ, F.coupling (0,lam)∈frontier highDomain ∧
          p (F.coupling (0,lam))^2≠1) ∧
        Negative.CompactNegativePhysicalObstruction F.coupling
          (Negative.NegativeRatioFamily.particleAmplitude F) (closedBall lam₀ ρ)

theorem joint_negative_family_conclusion : JointNegativeFamilyConclusion where
  general := by
    intro E inst1 inst2 Q curve amp b hQ hc ha hS hB hprime he hsq
    exact Negative.compact_normalized_negative_family_obstruction curve amp
      hQ hc ha hS hB hprime he hsq
  physical := by
    intro E inst1 inst2 Q curve amp b hQ hc ha hS hB hK hp hprime he hsq
    exact Negative.compact_negative_high_physical_obstruction curve amp
      hQ hc ha hS hB hK hp hprime he hsq
  actual_ratio := by
    intro b z₀ lam₀ hK hp hS hB hprime he hd
    exact Negative.exists_negative_high_ratio_family_obstruction hK hp hS hB hprime he hd
  actual_physical_ratio := by
    intro b z₀ lam₀ hK hp hS hB hprime he hd
    exact Negative.exists_negative_high_ratio_physical_obstruction hK hp hS hB hprime he hd

end
end IsingBulk.Joint
