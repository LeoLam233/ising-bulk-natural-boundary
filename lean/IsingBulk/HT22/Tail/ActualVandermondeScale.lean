import IsingBulk.HT22.Tail.SourceCollision
import IsingBulk.Preferred22.VandermondeScale

/-! Genuine full odd collision degree on every signed-mean source shell.
Only the generic polynomial norm and actual coordinate-difference estimate
are reused; no old transport bound or even-parity hypothesis occurs. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry
open scoped BigOperators

theorem sourceCoordinate_sub_eq_shared {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N) :
    sourceCoordinate τ p m s θ i-sourceCoordinate τ p m s θ j=
      preferredSourceCoordinate τ p m s θ i-preferredSourceCoordinate τ p m s θ j := by
  rw [←sourceCoordinate_moving_adapter,←sourceCoordinate_moving_adapter]
  ring

theorem actual_full_vandermonde_scale (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) →
      ‖preferredSquaredVandermonde (sourceCoordinate τ B.p B.m
        (IsingBulk.Branch.radialParameter d.alpha ε) θ)‖≤
        (C*(r/Real.sqrt (|μ|+r+ε)))^(N*(N-1)) := by
  obtain ⟨C,e,t,δ,hC,he,ht,hδ,hδB,hbound⟩ := preferred_actual_coordinate_difference d B
  refine ⟨C,e,t,δ,hC,he,ht,hδ,hδB,?_⟩
  intro N hN ε τ μ r hε hεr hτ hτr hr θ hθ hwindow
  apply preferredSquaredVandermonde_norm_le
  intro i j
  rw [sourceCoordinate_sub_eq_shared]
  simpa only [mul_div_assoc] using hbound N hN ε τ μ r hε hεr hτ hτr hr θ hθ hwindow i j

end
end IsingBulk.HT22.Tail
