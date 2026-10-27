import IsingBulk.Preferred22.CoefficientTailAssembly

/-! Connect the genuine transported absolute masses to actual complex
derivatives. The still-required global transport identity remains explicit;
no pointwise recurrence is silently substituted for an integral identity. -/
namespace IsingBulk.Preferred22
noncomputable section

/-- Precisely the large-order right integral identity. This separate
proposition makes no assertion about anchors or the finite intermediate block. -/
def PreferredLargeRightIntegralIdentity (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) (r : ℝ → ℝ) (k : ℕ) : Prop :=
  ∀ n : ℕ,2*k+4<n+1 → Even (n+1) → ∀ j : ℕ,j≤k →
    ∀ ε : ℝ,0<ε → ε<ε₀ →
    iteratedDeriv j (preferredTransportedIntegral (n := n) .right B.delta τ
      preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)=
    preferredTransportedIntegral (n := n) .right B.delta τ
      preferredPopulationCutoff B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)

/-- Exact derivative consequence of the proved q28 mass sum, conditional
only on the explicitly stated global right integral identity. -/
theorem preferred_large_right_derivative_tail_of_identity (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (r : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB r) (k : ℕ)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff r k)
    (hidentity : PreferredLargeRightIntegralIdentity d B τ ε₀ r k) :
    PreferredRightDerivativeTailStatement d B τ ε₀ r (2*k+4) k := by
  intro j hj
  obtain ⟨A,hA,hmass⟩ := preferred_complete_right_mass_tail_of_q28 d B r hcut k hq28 j hj
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  obtain ⟨hsum,hbound⟩ := hmass ε hε hεr
  have hn (m : ℕ) :
      0≤preferredRightDerivativeTailTerms d B τ r (2*k+4) j ε m := by
    unfold preferredRightDerivativeTailTerms
    split_ifs <;> positivity
  have hb (m : ℕ) : preferredRightDerivativeTailTerms d B τ r (2*k+4) j ε m≤
      preferredRightLargeMassTerms d B τ r k j ε m := by
    unfold preferredRightDerivativeTailTerms preferredRightLargeMassTerms
    split_ifs with hN
    · have hEven : Even (2*m+1+1) := ⟨m+1,by omega⟩
      rw [hidentity (2*m+1) (by omega) hEven j hj ε hε hεr]
      exact MeasureTheory.norm_integral_le_integral_norm _
    · exact le_rfl
  have hs := hsum.of_nonneg_of_le hn hb
  exact ⟨hs,(Summable.tsum_le_tsum hb hs hsum).trans hbound⟩

/-- Full right absolute mass, with every positive even order above Nstar. -/
def preferredRightAbsoluteMassTailTerms (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (r : ℝ → ℝ) (Nstar j : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  if Nstar<2*(m+1) then preferredRightAbsoluteTransportMass d B τ r (2*m+1) j ε else 0

def PreferredRightAbsoluteMassTail (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) (r : ℝ → ℝ) (Nstar k : ℕ) : Prop :=
  ∀ j : ℕ,j≤k → ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
    Summable (preferredRightAbsoluteMassTailTerms d B τ r Nstar j ε) ∧
    (∑' m,preferredRightAbsoluteMassTailTerms d B τ r Nstar j ε m)≤C*(1+|Real.log ε|)

/-- Full actual right derivatives follow from the literal complete right
absolute mass and full range of the global transport identity. -/
theorem preferred_right_derivative_tail_of_integrated_mass (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ ε₀ : ℝ) (r : ℝ → ℝ) (Nstar k : ℕ)
    (hEvenStar : Even Nstar)
    (hmass : PreferredRightAbsoluteMassTail d B τ ε₀ r Nstar k)
    (hidentity : PreferredTransportIntegralIdentity d B.delta τ preferredPopulationCutoff
      B.p B.m r Nstar k ε₀) :
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
      have hNN : Nstar+2≤2*m+1+1 := by
        obtain ⟨a,ha⟩ := hEvenStar
        omega
      rw [hidentity (2*m+1) hNN hEven j hj ε hε hεr .right]
      exact MeasureTheory.norm_integral_le_integral_norm _
    · exact le_rfl
  have hs := hsum.of_nonneg_of_le hn hle
  exact ⟨hs,(Summable.tsum_le_tsum hle hs hsum).trans hb⟩

end
end IsingBulk.Preferred22
