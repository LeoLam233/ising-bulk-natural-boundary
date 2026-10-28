import IsingBulk.HT22.First.LocalLimit.ThreeParticleSelected.ConstrainedMass
import IsingBulk.HT22.Selected.DensityDisk
import IsingBulk.HT22.Selected.DerivativeAssembly

/-! The N=3 selected term is separately proved, not omitted from the finite
complement or smuggled into the fourfold-convolution estimate. -/
namespace IsingBulk.HT22.LocalLimit.ThreeParticleSelected
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Selected Set MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem selected_three_particle_estimate (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ, 0<τ → τ<ρ → ∀ j : ℕ,
      ∃ C : ℝ, 0<C ∧ ∀ negative : Bool, ∀ ε : ℝ, 0<ε → ε<ρ →
      ‖iteratedDeriv j (selectedIntegral negative 2 τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖ ≤ C := by
  obtain ⟨c,H,A,J,ρ,hc,hH,hA,hJ,hρ,hρ1,hdata⟩ := selected_density_disk d hcap
  obtain ⟨D,hD,hprofile⟩ := signed_three_profile_constrained_mass d
  let B := cappedCanonicalPreferredBump d cap hcap
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro τ hτ hτρ j
  obtain ⟨K,hK,hbound⟩ := hdata τ hτ hτρ
  let R := c*τ^2/(3:ℝ)^3
  let M := J^3*(H*3/τ)*(K*Real.sqrt (3+1))^(3+1)*A^3 /
    (((3:ℕ).factorial:ℝ)*(2*Real.pi)^(3-1:ℕ))
  have hR : 0<R := by dsimp [R];positivity
  have hM : 0≤M := by dsimp [M];positivity
  let C := (j.factorial:ℝ)*M/R^j*D+1
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro negative ε hε hερ
  have hpoint : ∀ θ : Fin 3 → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      AnalyticOnNhd ℂ (selectedContinuedDensity (Physical.constraintSign negative) d B ε τ θ)
        (Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) ∧
      ∀ t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R,
        ‖selectedContinuedDensity (Physical.constraintSign negative) d B ε τ θ t‖≤
          M*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
    intro θ hw
    have hb (t : ℂ) (ht : t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) :=
      hbound 3 (by norm_num) ε hε hερ θ hw t
        (by simpa only [Metric.mem_closedBall,dist_eq_norm,R,Nat.cast_ofNat] using ht)
        (Physical.constraintSign negative) (Physical.constraintSign_norm negative)
    exact ⟨fun t ht => (hb t ht).1,fun t ht => (hb t ht).2⟩
  have hjet := selected_derivative_from_pointwise_disk negative 1 d B hε hτ.le hR hM j hpoint
  have hcoef : 0≤(j.factorial:ℝ)*M/R^j := by positivity
  have hmass := hprofile negative ε hε
  have hfinal := hjet.trans (mul_le_mul_of_nonneg_left hmass hcoef)
  exact hfinal.trans (by dsimp [C];linarith)

end
end IsingBulk.HT22.LocalLimit.ThreeParticleSelected
