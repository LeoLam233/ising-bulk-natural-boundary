import IsingBulk.Anisotropic.NegativeDominance.HighPoleEntropy

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm MeasureTheory Set Metric

/-- The actual ball-mass estimate (5.19), for every Taylor order and every
localized winding-sector subset, with the pole constructed internally. -/
theorem exists_actual_high_pole_entropy_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) :
    ∃r C : ℝ,0<r ∧ r≤1 ∧ 0<C ∧ ∀n : ℕ,1≤n → ∀d : ℝ,
      |d|<r → Real.pi/((n+1 : ℕ) : ℝ)≤|d| →
      ∃T : Config (n+1)→ℂ,AnalyticOnNhd ℂ T (ball 0 r) ∧ T 0=1-Complex.cos (d : ℂ) ∧
        (∀v : Config (n+1),‖v‖<r → poleEquation B phi hphi (d : ℂ) (T v) v=0) ∧
        ∀S : Set (Fin n→ℝ),S⊆smallConstrainedEnergyBall n r →
        ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,
        ‖∫x in S,χ x*poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖≤
          Real.exp (2*j*Real.log (n+1)-(n+1 : ℝ)^2/2*Real.log (n+1)+C*(n+1 : ℝ)^2) := by
  obtain ⟨r,M,c,hr,hr1,hM,hc,hbound⟩ :=
    exists_actual_high_pole_integral_bound B rootB phi hphi hB hrB hB0
  obtain ⟨C,hC,hentropy⟩ := highPoleEnvelope_entropy M c hM hc
  refine ⟨r,C,hr,hr1,hC,?_⟩
  intro n hn d hd hw
  obtain ⟨T,hTa,hT0,hTp,hTbound⟩ := hbound n hn d hd hw
  refine ⟨T,hTa,hT0,hTp,?_⟩
  intro S hS χ hχ j
  apply (hTbound S hS χ hχ j).trans
  simpa only [highPoleEnvelope,Nat.cast_add,Nat.cast_one] using hentropy (n+1) (by omega) j

end
end IsingBulk.Anisotropic.NegativeDominance
