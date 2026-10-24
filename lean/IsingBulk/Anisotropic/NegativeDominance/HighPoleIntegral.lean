import IsingBulk.Anisotropic.NegativeDominance.SmallConstrainedBall
import IsingBulk.Anisotropic.NegativeDominance.PoleCoefficientBound
import IsingBulk.Anisotropic.NegativeDominance.UniformSmallPole

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm MeasureTheory Set Metric
open scoped BigOperators
set_option maxHeartbeats 800000

/-- Actual all-order high-particle pole integrals. The analytic pole is constructed,
not supplied, and the constants precede every particle number, winding, order,
sector subset and bounded cutoff. No beta-integrability restriction is imposed. -/
theorem exists_actual_high_pole_integral_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) :
    ∃r M c : ℝ,0<r ∧ r≤1 ∧ 1≤M ∧ 0<c ∧ ∀n : ℕ,1≤n → ∀d : ℝ,
      |d|<r → Real.pi/((n+1 : ℕ) : ℝ)≤|d| →
      ∃T : Config (n+1)→ℂ,AnalyticOnNhd ℂ T (ball 0 r) ∧ T 0=1-Complex.cos (d : ℂ) ∧
        (∀v : Config (n+1),‖v‖<r → poleEquation B phi hphi (d : ℂ) (T v) v=0) ∧
        ∀S : Set (Fin n→ℝ),S⊆smallConstrainedEnergyBall n r →
        ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,
        ‖∫x in S,χ x*poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖≤
          (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1))*
            ((n+1 : ℝ)^2/2)^(j+1))*
          Real.exp (-((n+1 : ℝ)^2)/2*Real.log (n+1)+10*(n+1 : ℝ)^2) := by
  obtain ⟨δ,M,c,hδ,hM,hc,hcoef⟩ := poleTaylorIntegrand_uniform_bound B rootB phi hphi hB hrB hB0
  obtain ⟨ρ,hρ,hρδ,hpole⟩ := exists_uniform_small_pole B phi hphi hB hB0 δ hδ
  let r := min ρ 1
  have hr : 0<r := lt_min hρ (by norm_num)
  have hrρ : r≤ρ := min_le_left _ _
  have hrδ : r≤δ := hrρ.trans hρδ
  refine ⟨r,M,c,hr,min_le_right _ _,hM,hc,?_⟩
  intro n hn d hd hwind
  obtain ⟨T,hTa,hT0,hT⟩ := hpole (n+1) (by omega) (d : ℂ) (by simpa using hd.trans_le hrρ)
  refine ⟨T,hTa.mono (ball_subset_ball hrρ),hT0,?_,?_⟩
  · intro v hv
    exact (hT v (hv.trans_le hrρ)).1
  intro S hS χ hχ j
  let K : ℝ := 2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1))*
    ((n+1 : ℝ)^2/2)^(j+1)
  have hK : 0≤K := by dsimp [K]; positivity
  apply norm_integral_vandermonde_ball_bound hn S
    (hS.trans (smallConstrainedEnergyBall_subset hr.le (min_le_right _ _))) _ K hK
  intro x hx
  have hv := complexShape_norm_lt hr x (hS hx)
  have hTv := hT (complexShape x) (hv.trans_le hrρ)
  have hh := hcoef (n+1) (by omega) d T (shapeExtend x) (hd.trans_le hrδ) hTv.2
    (fun i => by
      have hi := (norm_le_pi_norm (complexShape x) i).trans_lt (hv.trans_le hrδ)
      simpa only [complexShape,Complex.norm_real,Real.norm_eq_abs] using hi)
    (complexShape_zeroMean x) hTv.1 hwind j
  have hχmul : ‖χ x*poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖≤
      ‖poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ x hx)
  apply hχmul.trans
  change ‖poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j
    (fun i => ((shapeExtend x i : ℝ) : ℂ))‖≤K*‖vandermonde (fun i => ((shapeExtend x i : ℝ) : ℂ))‖^2
  simpa only [K,Nat.cast_add,Nat.cast_one,mul_comm,mul_left_comm,mul_assoc] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
