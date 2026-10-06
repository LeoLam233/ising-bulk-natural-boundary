import IsingBulk.Tail.MixedCoefficientJetFamily
import IsingBulk.Tail.MixedGaussianAmplitudeJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Joint current-source jet family. The positive Gaussian coefficient is
chosen before the derivative order and survives the full density recurrence. -/
theorem mixed_current_source_jet_family (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ,0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,0<α → α<α₀ → 0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ A D : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 1≤A ∧ 0<D ∧
      ∀ (N : ℕ) (eps lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      sigma j=2 → sigma q≠2 →
      θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      let J := mixedBranchIndexSet sigma
      ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 →
      JetBound (mixedActiveBranchResidual J j q s φ y) 0 (order+1) ((N:ℝ)*A) ∧
      JetBound (mixedActiveCompactResidual J j q s φ y) 0 (order+1) ((N:ℝ)*A) ∧
      (∀ i,JetBound (mixedActiveAngularVelocity J j q s φ y i) 0 order ((N:ℝ)*A)) ∧
      JetBound (mixedActiveRegularAmplitude J q s φ y) 0 order
        (D^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2)) := by
  obtain ⟨ηF,hηF,hSetup⟩ := mixed_current_regular_amplitude_jets d hcsmall
  refine ⟨min ηF (Real.sin d.thetaB/4),lt_min hηF (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right ηF (Real.sin d.thetaB/4))
  obtain ⟨αF,τ₀,hαF,hτ₀,hSetup⟩ := hSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αF (Real.sin d.thetaB/4),τ₀,lt_min hαF (by positivity [d.a_pos]),hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  have hαsmall := hαlt.trans_le (min_le_right αF (Real.sin d.thetaB/4))
  obtain ⟨κ,hκ,hAmplitude⟩ := hSetup α τ hα (hαlt.trans_le (min_le_left _ _)) hτ hτlt
  refine ⟨κ,hκ,?_⟩
  intro order cap hcap
  obtain ⟨iF,hiF,hiFcap,hAmplitude⟩ := hAmplitude order cap hcap
  obtain ⟨iA,hiA,_,hCoefficients⟩ := mixed_actual_coefficient_jet_family d hcsmall cap hcap order
  refine ⟨min iF iA,lt_min hiF hiA,(min_le_left _ _).trans hiFcap,?_⟩
  intro inner hi hinner
  obtain ⟨cF,eF,tF,D,hcF,heF,htF,hD,hAmplitude⟩ := hAmplitude inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨cA,eA,tA,A,hcA,heA,htA,hA,hCoefficients⟩ := hCoefficients inner hi (hinner.trans (min_le_right _ _))
  refine ⟨min cF cA,min eF eA,min tF tA,A,D,lt_min hcF hcA,lt_min heF heA,lt_min htF htA,hA,hD,?_⟩
  intro N eps lam θ j q sigma l s hN heps hepslt hl0 hl1 htl hθ hσj hσq hSource hsupp hs
  dsimp only
  intro hsep
  have ha := hCoefficients η α hη hηsmall hα hαsmall N eps τ lam θ j q sigma l s hN heps
    (hepslt.trans_le (min_le_right _ _)) hτ.le hl0 hl1 (htl.trans_le (min_le_right _ _))
    hθ hσj hσq (Or.inr hSource) hsupp
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) heps.le)) hsep
  exact ⟨ha.1,ha.2.1,ha.2.2,hAmplitude N eps lam θ q sigma l s hN heps
    (hepslt.trans_le (min_le_left _ _)) hl0 hl1 (htl.trans_le (min_le_left _ _)) hθ hSource hsupp
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))⟩

/-- Original-source counterpart with the same inner-width flexibility.
The contour at lambda zero is the actual undeformed angle tuple. -/
theorem mixed_original_source_jet_family (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e A D : ℝ,0<c ∧ 0<e ∧ 1≤A ∧ 0<D ∧
      ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → θ∈angleBox N → sigma j=2 → sigma q≠2 →
      θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := angleTuple (Real.exp (-d.c₀*eps)) θ
      let φ := fun i => mixedSourcePhase s (y i)
      let J := mixedBranchIndexSet sigma
      ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 →
      JetBound (mixedActiveBranchResidual J j q s φ y) 0 (order+1) ((N:ℝ)*A) ∧
      JetBound (mixedActiveCompactResidual J j q s φ y) 0 (order+1) ((N:ℝ)*A) ∧
      (∀ i,JetBound (mixedActiveAngularVelocity J j q s φ y i) 0 order ((N:ℝ)*A)) ∧
      JetBound (mixedActiveRegularAmplitude J q s φ y) 0 order
        (D^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2)) := by
  obtain ⟨ηF,hηF,hSetup⟩ := mixed_original_regular_amplitude_jets d hcsmall
  refine ⟨min ηF (Real.sin d.thetaB/4),lt_min hηF (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right ηF (Real.sin d.thetaB/4))
  obtain ⟨αF,κ,hαF,hκ,hAmplitude⟩ := hSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αF (Real.sin d.thetaB/4),κ,lt_min hαF (by positivity [d.a_pos]),hκ,?_⟩
  intro α hα hαlt order cap hcap
  have hαsmall := hαlt.trans_le (min_le_right αF (Real.sin d.thetaB/4))
  obtain ⟨iF,hiF,hiFcap,hAmplitude⟩ := hAmplitude α hα (hαlt.trans_le (min_le_left _ _)) order cap hcap
  obtain ⟨iA,hiA,_,hCoefficients⟩ := mixed_actual_coefficient_jet_family d hcsmall cap hcap order
  refine ⟨min iF iA,lt_min hiF hiA,(min_le_left _ _).trans hiFcap,?_⟩
  intro inner hi hinner
  obtain ⟨cF,eF,D,hcF,heF,hD,hAmplitude⟩ := hAmplitude inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨cA,eA,tA,A,hcA,heA,htA,hA,hCoefficients⟩ := hCoefficients inner hi (hinner.trans (min_le_right _ _))
  refine ⟨min cF cA,min eF eA,A,D,lt_min hcF hcA,lt_min heF heA,hA,hD,?_⟩
  intro N eps θ j q sigma l s hN heps hepslt hθ hσj hσq hSource hsupp hs
  dsimp only
  intro hsep
  have ha := hCoefficients η α hη hηsmall hα hαsmall N eps 0 0 θ j q sigma l s hN heps
    (hepslt.trans_le (min_le_right _ _)) le_rfl le_rfl zero_le_one (by simpa using htA)
    hθ hσj hσq (Or.inl hSource) hsupp
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) heps.le))
  simp only [deformedPoint_zero] at ha
  obtain ⟨hR,hQ,hV⟩ := ha hsep
  exact ⟨hR,hQ,hV,hAmplitude N eps θ q sigma l s hN heps
    (hepslt.trans_le (min_le_left _ _)) hθ hSource hsupp
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))⟩

end
end IsingBulk.Tail
