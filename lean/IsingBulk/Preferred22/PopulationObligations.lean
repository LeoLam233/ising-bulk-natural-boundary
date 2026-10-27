import IsingBulk.Preferred22.ContourLift
import IsingBulk.Preferred22.ShellObligations

/-! Exact remaining selected-population and fixed-anchor estimates. These
are propositions about the literal source integrals, not supplied axioms.
The actual coefficient-to-piece decomposition is proved below. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff

/-- Manuscript Lemma 5.2, with its concrete population cutoff, normalized
full physical density, and constants preceding every particle order. -/
def PreferredSelectedPopulationBound (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 4≤n+1 → Even (n+1) →
    ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ‖iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖ ≤
          C*((n+1:ℕ):ℝ)^(3*j+1)*(C/Real.sqrt ((n+1:ℕ):ℝ))^(n+1)

/-- The entire named-anchor sum after the exact one-sided telescope. This
is the integrated factorial estimate required by Section 7.2; order two is
retained for the finite complement. The density/transport estimate itself
has not been assumed as a new axiom. -/
def PreferredAnchorAbsoluteBound (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) (r : ℝ → ℝ) (k : ℕ) : Prop :=
  ∀ j : ℕ, j≤k → ∃ C : ℝ, ∃ J : ℕ, 0<C ∧
    ∀ n : ℕ, 2≤n+1 → Even (n+1) → ∀ ε : ℝ, 0<ε → ε<ε₀ →
      (∑ a : Fin (n+1),
        ‖iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ
          preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)‖) ≤
        C^(n+1)*((n+1:ℕ):ℝ)^(-((n+1:ℕ):ℝ)/2+(J:ℝ))

/-- Exact connection from the complete constrained coefficient to every
actual term used in the right and anchor transport estimates. -/
theorem preferred_complete_transport_partition (n : ℕ) (he : Even (n+1))
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hrp : Function.Periodic r (2*Real.pi)) :
    coefficient (n+1) (IsingBulk.Branch.radialParameter d.alpha ε) =
      preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m
        (IsingBulk.Branch.radialParameter d.alpha ε) +
      2*(preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m r 0
        (IsingBulk.Branch.radialParameter d.alpha ε) +
        ∑ a : Fin (n+1), preferredTransportedIntegral (.anchor a) B.delta τ
          preferredPopulationCutoff B.p B.m r 0 (IsingBulk.Branch.radialParameter d.alpha ε)) := by
  rw [preferred_complete_population_partition n he d B hε hτ preferredPopulationCutoff
    preferredPopulationCutoff_smooth.continuous]
  rw [preferred_lower_integral_telescope n d B hε hτ preferredPopulationCutoff r
    preferredPopulationCutoff_smooth hr hrp]

end
end IsingBulk.Preferred22
