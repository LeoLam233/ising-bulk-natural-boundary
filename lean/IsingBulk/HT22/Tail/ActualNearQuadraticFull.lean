import IsingBulk.HT22.Tail.ActualNearScalarFull
import IsingBulk.HT22.Near.SourceAbsorption

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem actual_near_scalar_quadratic_full (d : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap₀ : ℝ, 0<cap₀ ∧ cap₀<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap₀ →
      ∃ cap ε₀ τ₀ δB D : ℝ, 0<cap ∧ cap<d.alpha ∧ 0<ε₀ ∧ 0<τ₀ ∧
        0<δB ∧ δB<B.delta ∧ 1≤D ∧
      ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ k : ℕ, ∃ E : ℝ, 1≤E ∧
      ∀ n : ℕ, ∀ ε τ μ r : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin (2*n+1) → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i≤B.delta) →
      (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) →
      ∀ i a : Fin (2*n+1), (∀ b, θ i≤θ b ∧ θ b≤θ a) → r≤θ a-θ i →
      ‖regularTransportedScalar τ preferredPopulationCutoff B.p B.m rcut k
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
      E^((2*n+1)^2)*
        (r/Real.sqrt (|μ|+r+ε))^((2*n+1)*(2*n))/(r/Real.sqrt (|μ|+r+ε))^(2*k) := by
  obtain ⟨cap₀,hcap₀,hcap₀a,hbound⟩ := actual_near_scalar_full d M hM
  refine ⟨cap₀,hcap₀,hcap₀a,?_⟩
  intro B hB
  obtain ⟨cap,e,t,b,D,hcap,hcapa,he,ht,hb,hbB,hD,hnear⟩ := hbound B hB
  refine ⟨cap,e,t,b,D,hcap,hcapa,he,ht,hb,hbB,hD,?_⟩
  intro rcut hrcut hperiod k
  obtain ⟨RA,Q,RB,RC,RV,hRA,hQ,hRB,hRC,hRV,hscalar⟩ := hnear rcut hrcut hperiod k
  obtain ⟨E,hE,habs⟩ := Near.source_near_prefactor_absorption
    (le_trans (by norm_num) hRA) (le_trans (by norm_num) hQ) hRB.le hRC.le hRV.le
    (le_trans (by norm_num) hD) k (k*k+6*k) (2*(k+1)+2) (2*k+2)
  refine ⟨E,hE,?_⟩
  intro n ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwin i a hext hgap
  have hh := hscalar n ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwin i a hext hgap
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact habs (2*n+1) (by omega) _ (Near.physical_normalizer_norm_ge_one _)

end
end IsingBulk.HT22.Tail
