import IsingBulk.Preferred22.WeightedRightRadialIntegral

/-! The actual source geometry closes the fixed smooth equality-exclusion
transport identity, with a common regime before all particle and derivative
orders. All smaller branch windows use the same literal multiplier and cutoff. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_weighted_right_integral_identity (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ n : ℕ,2≤n+1 → ∀ ψ : (Fin (n+1) → ℝ) → ℂ,ContDiff ℝ ∞ ψ →
      (∀ θ : Fin (n+1) → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0) →
      ∀ j : ℕ,∀ ε : ℝ,0<ε → ε<ε₀ →
        iteratedDeriv j (preferredWeightedRightIntegral n d B ψ τ rcut 0)
          (IsingBulk.Branch.radialParameter d.alpha ε)=
        preferredWeightedRightIntegral n d B ψ τ rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) := by
  obtain ⟨cg,hcg,hcga,hg⟩ := preferred_actual_regularDomain d
  obtain ⟨ct,hct,_hcta,ht⟩ := preferred_actual_right_tangency d
  refine ⟨min cg ct,lt_min hcg hct,(min_le_left _ _).trans_lt hcga,?_⟩
  intro B hB
  obtain ⟨δg,τg,εg,hδg,hδgB,hτg,hεg,hg'⟩ := hg B (hB.trans_le (min_le_left _ _))
  obtain ⟨δt,τt,εt,hδt,_hδtB,hτt,hεt,ht'⟩ := ht B (hB.trans_le (min_le_right _ _))
  let δ₀ := min δg δt
  let τ₀ := min τg τt
  let ε₀ := min εg εt
  refine ⟨δ₀,τ₀,ε₀,lt_min hδg hδt,(min_le_left _ _).trans_lt hδgB,
    lt_min hτg hτt,lt_min hεg hεt,?_⟩
  intro δB _hδB hδB₀ rcut hcut τ hτ hτr n hN ψ hψ hψzero
  have hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredPhysicalRegularDomain τ B.p B.m := by
    intro ε hε x hx hd
    apply hg' (n+1) hN ε τ hε.1 (hε.2.trans_le (min_le_left _ _)) hτ
      (hτr.trans_le (min_le_left _ _)) x _ hd
    intro i
    have hδBg : δB≤δg := hδB₀.trans (min_le_left _ _)
    exact ⟨by linarith [(hx i).1],(hx i).2⟩
  have htan : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0 := by
    intro ε hε x hx hd
    apply ht' (n+1) hN ε τ hε.1 (hε.2.trans_le (min_le_right _ _)) hτ
      (hτr.trans_le (min_le_right _ _)) x _ hd
    intro i
    have hδBt : δB≤δt := hδB₀.trans (min_le_right _ _)
    exact ⟨by linarith [(hx i).1],(hx i).2⟩
  exact preferred_weighted_right_integral_identity d B hτ ψ hψ hψzero rcut hcut hreg htan

end
end IsingBulk.Preferred22
