import IsingBulk.Anisotropic.NegativeDominance.PhysicalWindingOverhead
import IsingBulk.Anisotropic.NegativeDominance.PoleBetaIntegral

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm MeasureTheory Set Metric
open scoped Topology

/-- The actual higher-winding pole integral, with every particle normalization,
is exponentially smaller than the first-winding model once j dominates N².
This estimates the genuine pole integral; the separate contour comparison is
not hidden as a hypothesis or asserted here. -/
theorem exists_actual_higher_winding_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) (hr0 : rootB 0≠0) :
    ∃r C : ℝ,0<r ∧ 0<C ∧ ∃N0 : ℕ,∀n : ℕ,N0≤n → 2≤n → Odd (n+1) → ∀d : ℝ,
      |d|<r → |d|≤Real.pi → 3*Real.pi/(n+1)≤|d| →
      ∃T : Config (n+1)→ℂ,AnalyticOnNhd ℂ T (ball 0 r) ∧ T 0=1-Complex.cos (d : ℂ) ∧
        (∀v : Config (n+1),‖v‖<r → poleEquation B phi hphi (d : ℂ) (T v) v=0) ∧
        ∀S : Set (Fin n→ℝ),MeasurableSet S → S⊆smallConstrainedEnergyBall n r →
        ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,4*alpha (n+1)≤j →
        ‖∫x in S,χ x*poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖≤
          Real.exp (C*(n+1)^2)*(1/2 : ℝ)^(j/2)*
            ‖model (B (tau (n+1))) (rootB (tau (n+1)))
              (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1))
              (Real.sin phi) (n+1) j‖ := by
  obtain ⟨r,M,c,hr,hM,hc,hpole⟩ := exists_actual_pole_beta_integral_bound B rootB phi hphi hB hrB hB0
  obtain ⟨C,hC,hOver⟩ := physical_higherWindingOverhead_entropy B rootB phi M c hB hB0
    hrB.continuousAt hr0 hphi hM hc
  have he : ∀ᶠ N : ℕ in atTop,
      higherWindingOverhead M c (B (tau N)) (rootB (tau N))
        (hessianFactor (B (tau N)) (Real.cos phi) (Real.sin phi) N) (Real.sin phi) N≤Real.exp (C*(N : ℝ)^2) ∧
      B (tau N)≠0 ∧ rootB (tau N)≠0 ∧ hessianFactor (B (tau N)) (Real.cos phi) (Real.sin phi) N≠0 := by
    filter_upwards [hOver,tau_complex_tendsto_zero.eventually (hB.continuousAt.eventually_ne hB0),
      tau_complex_tendsto_zero.eventually (hrB.continuousAt.eventually_ne hr0),hessianFactor_eventually_nonzero B phi hB]
      with N hN hb hr' hH using ⟨hN,hb,hr',hH⟩
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp he
  refine ⟨r,C,hr,hC,N0,?_⟩
  intro n hn0 hn ho d hd hdπ hdw
  have hu := higher_winding_tau_gap (n+1) (by omega) d hdπ (by simpa using hdw)
  have htfirst := tau_pos (n+1) (by omega)
  have ht : 0<1-Real.cos d := lt_of_lt_of_le (by positivity : 0<2*tau (n+1)) hu
  obtain ⟨T,hTa,hT0,hT,hint⟩ := hpole n hn ho d hd ht
  refine ⟨T,hTa,hT0,hT,?_⟩
  intro S hSm hS χ hχ j hj
  have hest := hint S hSm hS χ hχ j (by omega)
  have hN := hN0 (n+1) (by omega)
  have hbeta := higher_winding_beta_model_bound M c (B (tau (n+1))) (rootB (tau (n+1)))
    (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1)) (Real.sin phi)
    ho (by omega) hj (by linarith) hc hN.2.1 hN.2.2.1 hN.2.2.2 hphi hu
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hN.1 (show 0≤(1/2 : ℝ)^(j/2) by positivity))
    (norm_nonneg (model (B (tau (n+1))) (rootB (tau (n+1)))
      (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1)) (Real.sin phi) (n+1) j))
  exact hest.trans (by simpa using hbeta.trans hbound)

end
end IsingBulk.Anisotropic.NegativeDominance
