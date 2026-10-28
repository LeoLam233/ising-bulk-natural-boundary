import IsingBulk.HT22.Selected.DensityDisk
import IsingBulk.HT22.Selected.DerivativeAssembly
import IsingBulk.HT22.Selected.SignedConvolution
import IsingBulk.HT22.Selected.FactorialEstimate

/-! The actual signed F001 selected term, with all fixed complex derivatives,
has a summable uniform odd-particle envelope. No tail hypothesis is exposed. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22 Set MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem selected_population_estimate (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ, 0<τ → τ<ρ → ∀ j : ℕ,
      ∃ C : ℝ, 0<C ∧ ∀ negative : Bool, ∀ n : ℕ, 2≤n →
      ∀ ε : ℝ, 0<ε → ε<ρ →
      ‖iteratedDeriv j (selectedIntegral negative (2*n) τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖ ≤
        C*(2*n+1:ℝ)^(3*j+2)*(C/Real.sqrt (2*n+1))^(2*n+1) := by
  obtain ⟨c,H,A,J,ρ,hc,hH,hA,hJ,hρ,hρ1,hdata⟩ := selected_density_disk d hcap
  obtain ⟨D,hD,hprofile⟩ := signed_profile_constrained_mass d
  let B := cappedCanonicalPreferredBump d cap hcap
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro τ hτ hτρ j
  obtain ⟨K,hK,hbound⟩ := hdata τ hτ hτρ
  obtain ⟨C,hC,hnum⟩ := selected_bordered_factorial_cauchy (mul_pos hJ hA) hK hH hD hc hτ j
  refine ⟨C,hC,?_⟩
  intro negative n hn ε hε hερ
  let N := 2*n+1
  let R := c*τ^2/(N:ℝ)^3
  let M := (H*(N:ℝ)/τ)*(J*A)^N*(K*Real.sqrt (N+1))^(N+1)/(N.factorial:ℝ)
  have hN : 0<N := by dsimp [N]; omega
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR : 0<R := by dsimp [R]; positivity
  have hM : 0≤M := by dsimp [M]; positivity
  have hpoint : ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      AnalyticOnNhd ℂ (selectedContinuedDensity (Physical.constraintSign negative) d B ε τ θ)
        (Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) ∧
      ∀ t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R,
        ‖selectedContinuedDensity (Physical.constraintSign negative) d B ε τ θ t‖≤
          M*(∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
    intro θ hw
    have hb (t : ℂ) (ht : t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) :=
      hbound N hN ε hε hερ θ hw t
        (by simpa only [Metric.mem_closedBall,dist_eq_norm,R] using ht)
        (Physical.constraintSign negative) (Physical.constraintSign_norm negative)
    refine ⟨fun t ht => (hb t ht).1,?_⟩
    intro t ht
    have hfac : 0<(N.factorial:ℝ) := by positivity
    have hperiod : 1≤(2*Real.pi)^(N-1) :=
      one_le_pow₀ (by linarith [Real.one_le_pi_div_two])
    have hden : (N.factorial:ℝ)≤(N.factorial:ℝ)*(2*Real.pi)^(N-1) :=
      le_mul_of_one_le_right hfac.le hperiod
    have hcoeff : J^N*(H*(N:ℝ)/τ)*(K*Real.sqrt (N+1))^(N+1)*A^N /
        ((N.factorial:ℝ)*(2*Real.pi)^(N-1))≤M := by
      calc
        _ ≤ J^N*(H*(N:ℝ)/τ)*(K*Real.sqrt (N+1))^(N+1)*A^N/(N.factorial:ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hfac hden
        _ = M := by dsimp [M]; rw [mul_pow]; ring
    exact (hb t ht).2.trans (mul_le_mul_of_nonneg_right hcoeff
      (Finset.prod_nonneg (fun i _ => (preferred_selected_oneBody_profile_pos d hε _).le)))
  have hjet := selected_derivative_from_pointwise_disk negative n d B hε hτ.le hR hM j hpoint
  have hcoef : 0≤(j.factorial:ℝ)*M/R^j := by positivity
  have hmass := hprofile negative (2*n) (by omega) ε hε
  have hfinal := hjet.trans ((mul_le_mul_of_nonneg_left hmass hcoef).trans (hnum N hN))
  simpa only [N,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hfinal

end
end IsingBulk.HT22.Selected
