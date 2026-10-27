import IsingBulk.Preferred22.ActualWeightedRightTransport
import IsingBulk.Preferred22.WeightedOuterMass

/-! Actual derivatives of the fixed equality-excluded physical right
integral obey the logarithmic estimate at every positive even order,
including N=2. The original multiplier is transported at every step;
periodic Stokes and the true coarea integral are already proved. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The weighted zeroth integral is literally the original punctured
physical integral; only its later descendants differ from ξ times Pj. -/
theorem preferredWeightedRightIntegral_equality_zero (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ)
    (rcut : ℝ → ℝ) (R ε : ℝ) :
    preferredWeightedRightIntegral n d B (preferredEqualityMultiplier R) τ rcut 0
      (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredPuncturedRightIntegral n d B τ rcut 0 R ε := by
  rfl

/-- The common physical regime is fixed before every N, derivative order
and equality radius. Smaller δB, τ and ε preserve the same actual cutoff
and original weighted integral. No full-tail or complement bound is assumed. -/
theorem preferred_actual_outer_right_derivative_log (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ n : ℕ,2≤n+1 → Even (n+1) → ∀ R : ℝ,0<R → ∀ j : ℕ,
      ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (preferredWeightedRightIntegral n d B (preferredEqualityMultiplier R) τ rcut 0)
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|) := by
  obtain ⟨ct,hct,hcta,ht⟩ := preferred_actual_weighted_right_integral_identity d
  obtain ⟨cm,hcm,_hcma,hm⟩ := preferred_actual_weighted_outer_mass d
  refine ⟨min ct cm,lt_min hct hcm,(min_le_left _ _).trans_lt hcta,?_⟩
  intro B hB
  obtain ⟨δt,τt,εt,hδt,hδtB,hτt,hεt,ht'⟩ := ht B (hB.trans_le (min_le_left _ _))
  obtain ⟨δm,τm,εm,hδm,_hδmB,hτm,hεm,hm'⟩ := hm B (hB.trans_le (min_le_right _ _))
  let δ₀ := min δt δm
  let τ₀ := min τt τm
  let ε₀ := min εt εm
  refine ⟨δ₀,τ₀,ε₀,lt_min hδt hδm,(min_le_left _ _).trans_lt hδtB,
    lt_min hτt hτm,lt_min hεt hεm,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr n hN hEven R hR j
  obtain ⟨A,hA,hb⟩ := hm' δB hδB (hδB₀.trans (min_le_right _ _)) rcut hcut τ hτ
    (hτr.trans_le (min_le_right _ _)) n hN hEven j R hR
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  rw [ht' δB hδB (hδB₀.trans (min_le_left _ _)) rcut hcut τ hτ
    (hτr.trans_le (min_le_left _ _)) n hN (preferredEqualityMultiplier R)
    (preferredEqualityMultiplier_smooth R) (preferredEqualityMultiplier_zero_germ R) j ε hε
    (hεr.trans_le (min_le_left _ _))]
  apply (norm_integral_le_lintegral_norm _).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hb ε hε (hεr.trans_le (min_le_right _ _)))).trans_eq
      (ENNReal.toReal_ofReal (by positivity))

end
end IsingBulk.Preferred22
