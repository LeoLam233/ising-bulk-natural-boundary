import IsingBulk.Preferred22.FirstInnerIntegral
import IsingBulk.Preferred22.ExcludedRightDerivativeLog
import IsingBulk.Preferred22.WeightedFactorPartition

/-! The actual first-order right contribution away from the unique
critical equal-angle chart is logarithmically bounded at every derivative
order. Noncritical equality disks and the genuine weighted whole-torus
transport are composed using an independent second equality radius. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_first_regular_factor_derivative_log (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (n : ℕ) (hN : n+1=2*p) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ σ : (Fin (n+1) → ℝ) → ℂ,ContDiff ℝ ∞ σ → (∀θ,‖σ θ‖≤1) →
      ∀ κ : ℝ,0<κ → (∀θ : Fin (n+1) → ℝ,(∀i,|θ i+d.alpha|<κ) → σ θ=0) →
      ∀ j : ℕ,∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (preferredWeightedRightIntegral n d B σ τ rcut 0)
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,houter⟩ := preferred_actual_outer_factor_derivative_log d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨δo,τo,εo,hδo,hδoB,hτo,hεo,ho⟩ := houter B hB
  obtain ⟨δi,Ri,τi,εi,hδi,hRi,hτi,hεi,hi⟩ :=
    preferred_actual_first_inner_factor_derivative_bound d hp hp5 ha hα n hN B
  refine ⟨min δo δi,min τo τi,min εo εi,lt_min hδo hδi,
    (min_le_left _ _).trans_lt hδoB,lt_min hτo hτi,lt_min hεo hεi,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr σ hσ hσb κ hκ hσzero j
  let R := min Ri (κ/2)
  have hR : 0<R := lt_min hRi (half_pos hκ)
  have hRi' : R≤Ri := min_le_left _ _
  have hRκ : R<κ := (min_le_right _ _).trans_lt (half_lt_self hκ)
  have hN2 : 2≤n+1 := by omega
  have hEven : Even (n+1) := ⟨p,by omega⟩
  obtain ⟨A,hA,ho'⟩ := ho δB hδB (hδB₀.trans (min_le_left _ _)) rcut hcut τ hτ
    (hτr.trans_le (min_le_left _ _)) n hN2 hEven σ hσ R hR j
  obtain ⟨C,hC,hi'⟩ := hi δB (hδB₀.trans (min_le_right _ _)) rcut hcut σ hσ hσb κ hκ hσzero
    R τ hR hRi' hRκ hτ (hτr.trans_le (min_le_right _ _)) j
  refine ⟨A+C,add_pos hA hC,?_⟩
  intro ε hε hεr
  have ho'' := ho' ε hε (hεr.trans_le (min_le_left _ _))
  have hi'' := hi' ε hε (hεr.trans_le (min_le_right _ _))
  rw [preferredWeightedRightIntegral_derivative_factor_partition n d B hτ
    (preferredEqualityMultiplier R) σ (preferredEqualityMultiplier_smooth R) hσ rcut hcut.2.2.1 j hε]
  calc
    _ ≤ ‖iteratedDeriv j (preferredWeightedRightIntegral n d B
        (fun θ => preferredEqualityMultiplier R θ*σ θ) τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖+
      ‖iteratedDeriv j (preferredWeightedRightIntegral n d B
        (fun θ => (1-preferredEqualityMultiplier R θ)*σ θ) τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖ := norm_add_le _ _
    _ ≤ A*(1+|Real.log ε|)+C := add_le_add ho'' hi''
    _ ≤ (A+C)*(1+|Real.log ε|) := by nlinarith [mul_nonneg hC.le (abs_nonneg (Real.log ε))]

end
end IsingBulk.Preferred22
