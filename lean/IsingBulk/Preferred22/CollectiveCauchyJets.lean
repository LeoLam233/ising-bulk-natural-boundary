import IsingBulk.Preferred22.SourceCollectiveNeighborhood
import IsingBulk.Preferred22.AnisotropicCauchy

/-! All fixed mixed complex parameter/q jets of the actual collective field.
The derivative-order constant is chosen before N, epsilon and configuration.
These are partial complex jets, not yet original source-frame derivatives. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual all-order anisotropic collective jet bound. A pure parameter
direction has weight one; a pure q direction has weight 1/diameter. Thus
every q derivative costs one diameter, while parameter jets cost none. -/
theorem preferred_actual_collective_mixed_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ n : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ∀ v : Fin n → ℂ × (Fin N → ℂ),
        let s := IsingBulk.Branch.radialParameter d.alpha ε
        let q := preferredSourceCoordinate τ B.p B.m s θ
        ‖iteratedFDeriv ℂ n
          (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) v‖≤
          C*(N:ℝ)^(2*n+2)/preferredAngularDiameter θ *
            ∏ k, max ‖(v k).1‖ (‖(v k).2‖/preferredAngularDiameter θ) := by
  obtain ⟨cap,hcap,hcapa,hfield⟩ := preferred_actual_collective_neighborhood d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨η,M,ε₀,τ₀,δB,hη,hM,hε₀,hτ₀,hδB,hδBB,hlocal⟩ := hfield B hBcap
  refine ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro n
  let C := cauchyJetConstant n*M/η^n
  have hC : 0<C := div_pos (mul_pos (cauchyJetConstant_pos n) hM) (pow_pos hη n)
  refine ⟨C,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam v
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  let diam := preferredAngularDiameter θ
  let a := η/(N:ℝ)^2
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := div_pos hη (sq_pos_of_pos hn)
  obtain ⟨hf,hb⟩ := hlocal N hN ε τ hε hεr hτ hτr θ hθ hdiam
  have haeq : a*diam=η*diam/(N:ℝ)^2 := by dsimp [a]; ring
  let F : ℂ × (Fin N → ℂ) → (Fin N → ℂ) := fun z => preferredResidualCollective z.1 z.2
  have hf' : AnalyticOnNhd ℂ (fun z : ℂ × (Fin N → ℂ) =>
      F (s+(a:ℂ)*z.1,q+((a*diam:ℝ):ℂ) • z.2)) (ball 0 1) := by
    rw [haeq]
    exact hf
  have hb' : ∀ z∈ball (0 : ℂ × (Fin N → ℂ)) 1,
      ‖F (s+(a:ℂ)*z.1,q+((a*diam:ℝ):ℂ) • z.2)‖≤M*(N:ℝ)^2/diam := by
    rw [haeq]
    exact hb
  have hh := anisotropic_cauchy_mixed_bound F (s,q) a diam (M*(N:ℝ)^2/diam)
    ha hdiam hf' hb' n v
  have hpow : (N:ℝ)^(2*n+2)=(N:ℝ)^2*((N:ℝ)^2)^n := by
    rw [pow_add,pow_mul]
    ring
  convert hh using 1
  rw [hpow]
  dsimp only [C,a]
  rw [div_pow]
  field_simp [hη.ne',hn.ne',hdiam.ne',diam]
  dsimp only [diam]
  ring

end
end IsingBulk.Preferred22
