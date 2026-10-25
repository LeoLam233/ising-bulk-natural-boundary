import IsingBulk.Joint.Negative.FamilyPhysicalMixedTails

namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric
open scoped Topology

/-- One common actual high-domain tube and summable envelopes for EVERY ambient
mixed derivative of the literal full HT particle tail. The geometric side and
all estimates are conclusions; no continuation or derivative oracle is assumed. -/
structure JointNegativeMixedFamilyConclusion : Prop where
  physical_mixed : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b : ℝ} (curve : ℂ × E→Coupling) {Q : Set E},
    |b|<1 → IsCompact Q →
    (∀eta∈Q,AnalyticAt ℂ curve (0,eta)) →
    (∀eta∈Q,curve (0,eta)∈frontier highDomain) →
    (∀eta∈Q,p (curve (0,eta))^2≠1) →
    (∀eta∈Q,S (curve (0,eta))≠0) →
    (∀eta∈Q,(transferB (curve (0,eta))).im<0) →
    (∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t) →
    ∃δ : ℝ,0<δ ∧
      (∀eta∈Q,∀u : ℂ,‖u‖<δ →
        (curve (u,eta)∈highDomain ↔ 0<(transferB (curve (u,eta))*u).im)) ∧
      ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<(transferB (curve (u,eta))*u).im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>Transverse.highFullParticle (j+2+k) (curve q)) (u,eta)‖≤G k

theorem joint_negative_mixed_family_conclusion : JointNegativeMixedFamilyConclusion where
  physical_mixed := @Negative.compact_negative_high_physical_mixed_tails_on_common_tube

end
end IsingBulk.Joint
