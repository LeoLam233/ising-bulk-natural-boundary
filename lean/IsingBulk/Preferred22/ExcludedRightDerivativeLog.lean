import IsingBulk.Preferred22.ActualWeightedRightTransport
import IsingBulk.Preferred22.WeightedExcludedMass

/-! Genuine derivative estimates for every smooth original multiplier
vanishing in a fixed full-equality neighborhood. This permits a second
independent equality cutoff after selecting the local critical chart. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The common physical regime is fixed before every N, derivative order
and equality radius. Smaller δB, τ and ε preserve the same actual cutoff
and original weighted integral. No full-tail or complement bound is assumed. -/
theorem preferred_actual_excluded_right_derivative_log (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ n : ℕ,2≤n+1 → Even (n+1) →
      ∀ ψ : (Fin (n+1) → ℝ) → ℂ,ContDiff ℝ ∞ ψ → ∀ ρ : ℝ,0<ρ →
      (∀ θ : Fin (n+1) → ℝ,preferredAngularDiameter θ<ρ → ψ=ᶠ[𝓝 θ] fun _ => 0) → ∀ j : ℕ,
      ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (preferredWeightedRightIntegral n d B ψ τ rcut 0)
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|) := by
  obtain ⟨ct,hct,hcta,ht⟩ := preferred_actual_weighted_right_integral_identity d
  obtain ⟨cm,hcm,_hcma,hm⟩ := preferred_actual_weighted_excluded_mass d
  refine ⟨min ct cm,lt_min hct hcm,(min_le_left _ _).trans_lt hcta,?_⟩
  intro B hB
  obtain ⟨δt,τt,εt,hδt,hδtB,hτt,hεt,ht'⟩ := ht B (hB.trans_le (min_le_left _ _))
  obtain ⟨δm,τm,εm,hδm,_hδmB,hτm,hεm,hm'⟩ := hm B (hB.trans_le (min_le_right _ _))
  let δ₀ := min δt δm
  let τ₀ := min τt τm
  let ε₀ := min εt εm
  refine ⟨δ₀,τ₀,ε₀,lt_min hδt hδm,(min_le_left _ _).trans_lt hδtB,
    lt_min hτt hτm,lt_min hεt hεm,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr n hN hEven ψ hψ ρ hρ hψzero j
  obtain ⟨A,hA,hb⟩ := hm' δB hδB (hδB₀.trans (min_le_right _ _)) rcut hcut τ hτ
    (hτr.trans_le (min_le_right _ _)) n hN hEven ψ hψ ρ hρ hψzero j
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  rw [ht' δB hδB (hδB₀.trans (min_le_left _ _)) rcut hcut τ hτ
    (hτr.trans_le (min_le_left _ _)) n hN ψ
    hψ (fun θ hd => hψzero θ (by simpa only [hd] using hρ)) j ε hε
    (hεr.trans_le (min_le_left _ _))]
  apply (norm_integral_le_lintegral_norm _).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hb ε hε (hεr.trans_le (min_le_right _ _)))).trans_eq
      (ENNReal.toReal_ofReal (by positivity))


/-- Multiplication by any fixed smooth shape factor preserves the exact
open equality exclusion, before the physical transport recursion. -/
theorem preferredEqualityMultiplier_mul_zero_germ {N : ℕ} (hN : 0<N)
    {R : ℝ} (hR : 0<R) (σ : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ)
    (hd : preferredAngularDiameter θ<R/(2*(N:ℝ))) :
    (fun x => preferredEqualityMultiplier R x*σ x)=ᶠ[𝓝 θ] fun _ => 0 := by
  filter_upwards [preferredEqualityMultiplier_zero_germ_small hN hR θ hd] with x hx
  rw [hx,zero_mul]

/-- Source-specific fixed-exclusion estimate with an arbitrary smooth
original factor. No derivative norm assumption on a descendant is used. -/
theorem preferred_actual_outer_factor_derivative_log (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ n : ℕ,2≤n+1 → Even (n+1) →
      ∀ σ : (Fin (n+1) → ℝ) → ℂ,ContDiff ℝ ∞ σ → ∀ R : ℝ,0<R → ∀ j : ℕ,
      ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (preferredWeightedRightIntegral n d B
          (fun θ => preferredEqualityMultiplier R θ*σ θ) τ rcut 0)
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,hall⟩ := preferred_actual_excluded_right_derivative_log d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀B,hτ₀,hε₀,hb⟩ := hall B hB
  refine ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀B,hτ₀,hε₀,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr n hN hEven σ hσ R hR j
  exact hb δB hδB hδB₀ rcut hcut τ hτ hτr n hN hEven
    (fun θ => preferredEqualityMultiplier R θ*σ θ) ((preferredEqualityMultiplier_smooth R).mul hσ)
    (R/(2*((n+1:ℕ):ℝ))) (by positivity)
    (preferredEqualityMultiplier_mul_zero_germ (by omega) hR σ) j

end
end IsingBulk.Preferred22
