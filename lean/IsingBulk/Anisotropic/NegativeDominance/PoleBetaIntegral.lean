import IsingBulk.Anisotropic.NegativeDominance.PoleBetaIntegrand
import IsingBulk.Anisotropic.NegativeDominance.UniformSmallPole

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm MeasureTheory Set Metric

/-- Actual winding pole integrals are bounded by the exact full constrained
beta period. All branch, residue and energy estimates are derived internally. -/
theorem exists_actual_pole_beta_integral_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) :
    ∃r M c : ℝ,0<r ∧ 1≤M ∧ 0<c ∧ ∀n : ℕ,2≤n → Odd (n+1) → ∀d : ℝ,
      |d|<r → 0<1-Real.cos d →
      ∃T : Config (n+1)→ℂ,AnalyticOnNhd ℂ T (ball 0 r) ∧ T 0=1-Complex.cos (d : ℂ) ∧
        (∀v : Config (n+1),‖v‖<r → poleEquation B phi hphi (d : ℂ) (T v) v=0) ∧
        ∀S : Set (Fin n→ℝ),MeasurableSet S → S⊆smallConstrainedEnergyBall n r →
        ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,alpha (n+1)≤j →
        ‖∫x in S,χ x*poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖≤
          (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1)))*
            constrainedBetaValue (n+1) j (1-Real.cos d) (1/(4*(n+1))) := by
  obtain ⟨δ,M,c,hδ,hM,hc,hcoef⟩ := poleTaylorIntegrand_beta_uniform_bound B rootB phi hphi hB hrB hB0
  obtain ⟨r,hr,hrδ,hpole⟩ := exists_uniform_small_pole B phi hphi hB hB0 δ hδ
  refine ⟨r,M,c,hr,hM,hc,?_⟩
  intro n hn ho d hd hτ
  obtain ⟨T,hTa,hT0,hT⟩ := hpole (n+1) (by omega) (d : ℂ) (by simpa using hd)
  refine ⟨T,hTa,hT0,fun v hv => (hT v hv).1,?_⟩
  intro S hSm hS χ hχ j hj
  apply norm_integral_constrained_beta_bound ho hn j hj (1-Real.cos d) (1/(4*(n+1)))
    hτ (by positivity) S hSm _ _ (by positivity)
  intro x hx
  have hv := complexShape_norm_lt hr x (hS hx)
  have hTv := hT (complexShape x) hv
  have hh := hcoef n d T x (hd.trans_le hrδ) hTv.2
    (fun i => by
      have hi := (norm_le_pi_norm (complexShape x) i).trans_lt (hv.trans_le hrδ)
      simpa only [complexShape,Complex.norm_real,Real.norm_eq_abs] using hi)
    hTv.1 hτ j
  calc
    _ ≤ ‖poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ x hx)
    _ ≤ _ := hh

end
end IsingBulk.Anisotropic.NegativeDominance
