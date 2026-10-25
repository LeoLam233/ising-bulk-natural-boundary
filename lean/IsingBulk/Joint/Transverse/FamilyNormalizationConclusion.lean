import IsingBulk.Joint.Transverse.FamilyNormalization

namespace IsingBulk.Joint
noncomputable section
open Transverse

/-- Actual common analytic normalization for every finite complex parameter
polydisk. Both inverse identities and the common radius are contained in the
constructed structure, not supplied as hypotheses. -/
structure JointFamilyNormalizationConclusion : Prop where
  normalize : ∀(d : ℕ) (f : ℂ × (Fin d→ℂ)→ℂ) (eta₀ : Fin d→ℂ),
    AnalyticAt ℂ f (0,eta₀) → f (0,eta₀)=0 →
    deriv (fun z=>f (z,eta₀)) 0≠0 → Nonempty (FamilyNormalization f eta₀)

theorem joint_family_normalization_conclusion : JointFamilyNormalizationConclusion where
  normalize := fun _ _ _ hf hz hd=>exists_familyNormalization hf hz hd

end
end IsingBulk.Joint
