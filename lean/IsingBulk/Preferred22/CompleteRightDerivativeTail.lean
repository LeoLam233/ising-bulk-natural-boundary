import IsingBulk.Preferred22.RightDerivativeTail

/-! The complete right derivative bridge needs only the right-cell identity.
The anchor cells remain a separate source obligation. -/
namespace IsingBulk.Preferred22
noncomputable section

def PreferredRightIntegralIdentity (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) (r : ℝ → ℝ) (Nstar k : ℕ) : Prop :=
  ∀ n : ℕ,Nstar<n+1 → Even (n+1) → ∀ j : ℕ,j≤k →
    ∀ ε : ℝ,0<ε → ε<ε₀ →
    iteratedDeriv j (preferredTransportedIntegral (n := n) .right B.delta τ
      preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)=
    preferredTransportedIntegral (n := n) .right B.delta τ
      preferredPopulationCutoff B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)

/-- Actual full right derivatives, at every positive even order above Nstar,
follow from the exact right integral identity and genuine absolute mass sum. -/
theorem preferred_complete_right_derivative_tail_of_mass_identity (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ ε₀ : ℝ) (r : ℝ → ℝ) (Nstar k : ℕ)
    (hmass : PreferredRightAbsoluteMassTail d B τ ε₀ r Nstar k)
    (hidentity : PreferredRightIntegralIdentity d B τ ε₀ r Nstar k) :
    PreferredRightDerivativeTailStatement d B τ ε₀ r Nstar k := by
  intro j hj
  obtain ⟨C,hC,hbound⟩ := hmass j hj
  refine ⟨C,hC,?_⟩
  intro ε hε hεr
  obtain ⟨hsum,hb⟩ := hbound ε hε hεr
  have hn (m : ℕ) : 0≤preferredRightDerivativeTailTerms d B τ r Nstar j ε m := by
    unfold preferredRightDerivativeTailTerms
    split_ifs <;> positivity
  have hle (m : ℕ) : preferredRightDerivativeTailTerms d B τ r Nstar j ε m≤
      preferredRightAbsoluteMassTailTerms d B τ r Nstar j ε m := by
    unfold preferredRightDerivativeTailTerms preferredRightAbsoluteMassTailTerms
    split_ifs with hN
    · have hEven : Even (2*m+1+1) := ⟨m+1,by omega⟩
      rw [hidentity (2*m+1) (by omega) hEven j hj ε hε hεr]
      exact MeasureTheory.norm_integral_le_integral_norm _
    · exact le_rfl
  have hs := hsum.of_nonneg_of_le hn hle
  exact ⟨hs,(Summable.tsum_le_tsum hle hs hsum).trans hb⟩


end
end IsingBulk.Preferred22
