import IsingBulk.Joint.Isotropic.CompleteDescendants
import IsingBulk.Joint.Isotropic.DeckGroup
import IsingBulk.Joint.Isotropic.CompleteNormalization

namespace IsingBulk.Joint
noncomputable section
open Set Anisotropic

/-- The isotropic conclusion includes the actual complete normalized functions,
their relation to the joint functions, every circle point, and the global LT
deck group. No global exterior inverse temperature occurs in the statement. -/
structure JointIsotropicConclusion : Prop where
  high_bijective : BijOn Complex.sinh (omegaH 1) {s : ℂ | ‖s‖ < 1}
  high_forward_analytic : AnalyticOnNhd ℂ Complex.sinh (omegaH 1)
  high_inverse_analytic : AnalyticOnNhd ℂ IsingBulk.Final.arsinhRight {s : ℂ | ‖s‖ < 1}
  high_inverse : ∀ z ∈ omegaH 1, IsingBulk.Final.arsinhRight (Complex.sinh z) = z
  low_covering : IsCoveringMap lowSinhMap
  low_simply_connected : IsSimplyConnected (omegaL 1)
  low_deck : ∀ g : deck lowSinhMap,
    ∃! n : ℤ, (g : omegaL 1 ≃ₜ omegaL 1) = lowDeckTranslation n
  low_deck_group : Nonempty (Multiplicative ℤ ≃* deck lowSinhMap)
  high_descent : ∀ z ∈ omegaH 1, FormFactors.highNormalizedBulk (ratioSlice 1 z) =
    IsingBulk.HT.Final.interiorFullBulk (Complex.sinh z)
  low_descent : ∀ z ∈ omegaL 1, FormFactors.lowNormalizedBulk (ratioSlice 1 z) =
    IsingBulk.Tail.exteriorNormalizedBulk (Complex.sinh z)
  low_deck_invariant : ∀ (z : ℂ) (n : ℤ),
    FormFactors.lowNormalizedBulk (ratioSlice 1 (z+n*(2*Real.pi*Complex.I))) =
      FormFactors.lowNormalizedBulk (ratioSlice 1 z)
  high_origin : IsingBulk.HT.Final.interiorFullBulk 0 = 1
  high_full_odd : ∀ s : ℂ, s≠0 → IsingBulk.HT.Final.interiorFullBulk s =
    (1-s^4)^(1/4:ℂ)/s * ∑' n : ℕ, IsingBulk.HT.Final.exteriorOddTerm n (s⁻¹)
  low_connected : ∀ s : ℂ, IsingBulk.Tail.exteriorNormalizedBulk s =
    1-(1-(s^4)⁻¹)^(1/4:ℂ) + 2*(1-(s^4)⁻¹)^(1/4:ℂ) *
      ∑' n : ℕ, IsingBulk.Tail.exteriorEvenTerm n s
  low_full_even : ∀ z ∈ omegaL 1,
    IsingBulk.Tail.exteriorNormalizedBulk (Complex.sinh z) =
      FormFactors.lowPrefactor (ratioSlice 1 z) *
        ∑' n : ℕ, p (ratioSlice 1 z)^(n+1) *
          FormFactors.unscaledFullCoefficient (2*n+2) (ratioSlice 1 z)
  high_fullsite : ∀ z ∈ omegaH 1,
    IsingBulk.HT.Final.interiorFullBulk (Complex.sinh z) =
      FormFactors.highPrefactor (ratioSlice 1 z) *
        ∑' n : ℕ, p (ratioSlice 1 z)^n *
          FormFactors.unscaledFullCoefficient (2*n+1) (ratioSlice 1 z)
  high_boundary : HolomorphicNaturalBoundaryOn {s : ℂ | ‖s‖ < 1}
    IsingBulk.HT.Final.interiorFullBulk
  low_boundary : HolomorphicNaturalBoundaryOn {s : ℂ | 1 < ‖s‖}
    IsingBulk.Tail.exteriorNormalizedBulk

theorem joint_isotropic_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    JointIsotropicConclusion where
  high_bijective := high_biholomorphism.1
  high_forward_analytic := high_biholomorphism.2.1
  high_inverse_analytic := high_biholomorphism.2.2.1
  high_inverse := high_biholomorphism.2.2.2
  low_covering := low_universal_covering.1
  low_simply_connected := low_universal_covering.2
  low_deck := low_deck_classification
  low_deck_group := ⟨lowDeckGroupEquiv⟩
  high_descent := fun _ hz => joint_high_isotropic_identity hz
  low_descent := fun _ hz => joint_low_isotropic_identity (hphys 1 (by norm_num)) hz
  low_deck_invariant := low_bulk_deck_invariant
  high_origin := high_descendant_zero
  high_full_odd := fun _ hs => high_descendant_complete_odd_formula hs
  low_connected := low_descendant_complete_connected_formula
  low_full_even := fun _ hz => low_descendant_complete_fullsite_formula hphys hz
  high_fullsite := fun _ hz => high_descendant_complete_fullsite_formula hz
  high_boundary := high_descendant_componentwise hphys
  low_boundary := low_descendant_componentwise hphys

end
end IsingBulk.Joint
