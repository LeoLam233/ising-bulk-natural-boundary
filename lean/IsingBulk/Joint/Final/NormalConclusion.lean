import IsingBulk.Joint.FormFactors.CompactNormal

namespace IsingBulk.Joint
noncomputable section
open Set Filter FormFactors

/-- Literal normal convergence and all mixed jets of the complete normalized
odd/even series, not a replacement function defined from separate slices. -/
structure JointNormalConclusion : Prop where
  high_holomorphic : DifferentiableOn ℂ highNormalizedBulk highDomain
  high_jets : ∀ K ∈ highDomain, ∀ j : ℕ,
    HasSum (fun n => iteratedFDeriv ℂ j (fun t => highPrefactor t*(p t^(n)*unscaledFullCoefficient (2*n+1) t)) K)
      (iteratedFDeriv ℂ j highNormalizedBulk K)
  high_majorant : ∀ C : Set Coupling, IsCompact C → C⊆highDomain → ∀ j : ℕ,
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ n, 0≤M n) ∧ ∀ n K, K∈C →
      ‖iteratedFDeriv ℂ j (fun t => highPrefactor t*(p t^(n)*unscaledFullCoefficient (2*n+1) t)) K‖≤M n
  high_uniform : ∀ C : Set Coupling, IsCompact C → C⊆highDomain → ∀ j : ℕ,
    TendstoUniformlyOn (fun m K => ∑ n ∈ Finset.range m,
      iteratedFDeriv ℂ j (fun t => highPrefactor t*(p t^(n)*unscaledFullCoefficient (2*n+1) t)) K)
      (iteratedFDeriv ℂ j highNormalizedBulk) atTop C
  low_holomorphic : DifferentiableOn ℂ lowNormalizedBulk lowDomain
  low_jets : ∀ K ∈ lowDomain, ∀ j : ℕ,
    HasSum (fun n => iteratedFDeriv ℂ j (fun t => lowPrefactor t*(p t^(n+1)*unscaledFullCoefficient (2*n+2) t)) K)
      (iteratedFDeriv ℂ j lowNormalizedBulk K)
  low_majorant : ∀ C : Set Coupling, IsCompact C → C⊆lowDomain → ∀ j : ℕ,
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ n, 0≤M n) ∧ ∀ n K, K∈C →
      ‖iteratedFDeriv ℂ j (fun t => lowPrefactor t*(p t^(n+1)*unscaledFullCoefficient (2*n+2) t)) K‖≤M n
  low_uniform : ∀ C : Set Coupling, IsCompact C → C⊆lowDomain → ∀ j : ℕ,
    TendstoUniformlyOn (fun m K => ∑ n ∈ Finset.range m,
      iteratedFDeriv ℂ j (fun t => lowPrefactor t*(p t^(n+1)*unscaledFullCoefficient (2*n+2) t)) K)
      (iteratedFDeriv ℂ j lowNormalizedBulk) atTop C

theorem joint_normal_conclusion : JointNormalConclusion where
  high_holomorphic := highNormalizedBulk_differentiableOn
  high_jets := fun _ h j => highNormalizedBulk_all_mixed_derivatives h j
  high_majorant := fun _ hc hd j => highNormalizedBulk_compact_normal_majorant hc hd j
  high_uniform := fun _ hc hd j => highNormalizedBulk_uniform_jets_on_compact hc hd j
  low_holomorphic := lowNormalizedBulk_differentiableOn
  low_jets := fun _ h j => lowNormalizedBulk_all_mixed_derivatives h j
  low_majorant := fun _ hc hd j => lowNormalizedBulk_compact_normal_majorant hc hd j
  low_uniform := fun _ hc hd j => lowNormalizedBulk_uniform_jets_on_compact hc hd j

end
end IsingBulk.Joint
