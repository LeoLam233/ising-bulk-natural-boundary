import IsingBulk.HT22.Anchor.ActualAmplitude
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem raw_amplitude_bound_normalize {N : ℕ} (hN : 0<N)
    {H A : ℝ} (hH : 0≤H) (hA : 0≤A) :
    H*(Real.sqrt (N+1:ℕ)*A^3)^(N+1)*A^N/(N.factorial:ℝ) ≤
      (H*A^3)*((4*Real.exp 1*A^4)/Real.sqrt N)^N*(N:ℝ) := by
  have he : H*(Real.sqrt (N+1:ℕ)*A^3)^(N+1)*A^N/(N.factorial:ℝ) =
      H*A^3*(A^4)^N*((Real.sqrt (N+1:ℕ))^(N+1)/(N.factorial:ℝ)) := by
    simp only [mul_pow,pow_succ]
    ring
  rw [he]
  calc
    _ ≤ H*A^3*(A^4)^N*((N:ℝ)*((4*Real.exp 1)/Real.sqrt N)^N) :=
      mul_le_mul_of_nonneg_left (HT22.bordered_hadamard_factorial_envelope hN) (by positivity)
    _ = _ := by
      rw [show (4*Real.exp 1*A^4)/Real.sqrt N=A^4*((4*Real.exp 1)/Real.sqrt N) by ring,mul_pow]
      ring

/-- Factorial-decaying analytic amplitude balls, with exactly one extra N
from the constant border. Both resolvent signs have the same constants. -/
theorem actual_amplitude_normalized_balls (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ c A H : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<c ∧ 0<A ∧ 0<H ∧
      ∀ N : ℕ,0<N → ∀ σ : ℂ,‖σ‖=1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ anchor : Fin N,θ anchor≤ -d.b-δB/2 →
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      ∃ F : (ℂ × (Fin N → ℂ)) → ℂ,
        (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2) =ᶠ[𝓝 (s,q)] F ∧
        AnalyticOnNhd ℂ F (closedBall (s,q) (c/(N:ℝ))) ∧
        ∀ z∈closedBall (s,q) (c/(N:ℝ)),‖F z‖≤H*(A/Real.sqrt N)^N*(N:ℝ) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_amplitude_balls d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨ε₀,τ₀,c,A,H,hε₀,hτ₀,hc,hA,hH,hball⟩ := hsource B hB δB hδB
  refine ⟨ε₀,τ₀,c,4*Real.exp 1*A^4,H*A^3,hε₀,hτ₀,hc,by positivity,by positivity,?_⟩
  intro N hN σ hσ ε τ hε hεr hτ hτr θ hθ anchor hanchor
  obtain ⟨F,he,ha,hb⟩ := hball N hN σ hσ ε τ hε hεr hτ hτr θ hθ anchor hanchor
  exact ⟨F,he,ha,fun z hz => (hb z hz).trans (raw_amplitude_bound_normalize hN hH.le hA.le)⟩
end
end IsingBulk.HT22.Anchor
