import IsingBulk.Anisotropic.NegativeCycles.ActualInnerIntegral
import IsingBulk.Anisotropic.NegativeCycles.ShiftedInnerPole
import IsingBulk.Anisotropic.NegativeNormalForm.FullDensityEnvelope

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric MeasureTheory NegativeNormalForm
set_option maxHeartbeats 800000

/-- The integrated remainder estimate instantiated at the already constructed
actual pole witness. No analytic-remainder or derivative-exchange premise. -/
theorem exists_actual_witness_remainder (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ (R₀ : ℂ → ℂ) (ρ c σ C M : ℝ), 0<ρ ∧ 0<c ∧ 0<σ ∧ 0<C ∧ 1≤M ∧
      ∀ m : ℕ, ∀ d : ℂ, ‖d‖<ρ →
      ∀ P : UniformProjectedWitness B phi hphi (2*m+1) d rP CP,
      ∀ (K : Set (Fin (2*m) → ℝ)) (μ : Measure (Fin (2*m) → ℝ)),
      IsFiniteMeasureOnCompacts μ → IsCompact K →
      ∀ psi : (Fin (2*m) → ℝ) → Config (2*m+1), Continuous psi →
      (∀ x∈K, absoluteEnergy (psi x)<σ) →
      let F := fun t => ∫ x in K,
        actualInnerRemainder B rootB phi hphi R₀ m (psi x) (shiftedInnerPole d P.T (psi x)) t ∂μ
      AnalyticOnNhd ℂ F (ball 0 (c/(2*m+1:ℕ))) ∧
      (∀ j : ℕ, ‖iteratedDeriv j F 0/(j.factorial:ℂ)‖≤
        ((μ K).toReal*(C*remainderGaussianEnvelope M m))/((c/(2*m+1:ℕ))/2)^j) ∧
      (∀ j : ℕ, iteratedDeriv j F 0=∫ x in K,
        iteratedDeriv j (actualInnerRemainder B rootB phi hphi R₀ m
          (psi x) (shiftedInnerPole d P.T (psi x))) 0 ∂μ) ∧
      (∀ x∈K, ∀ t∈ball 0 (c/(2*m+1:ℕ)), t≠shiftedInnerPole d P.T (psi x) →
        formFactorNumerator B rootB phi hphi 0 t (psi x)*
          cothHalf (fun u => poleEquation B phi hphi 0 u (psi x)) t=
        (-2*formFactorNumerator B rootB phi hphi 0 (shiftedInnerPole d P.T (psi x)) (psi x)/
          poleParameterDerivative B phi hphi 0 (shiftedInnerPole d P.T (psi x)) (psi x))/
          (shiftedInnerPole d P.T (psi x)-t)+
        actualInnerRemainder B rootB phi hphi R₀ m (psi x) (shiftedInnerPole d P.T (psi x)) t) ∧
      (∀ t∈ball 0 (c/(2*m+1:ℕ)), IntegrableOn
        (fun x => actualInnerRemainder B rootB phi hphi R₀ m (psi x)
          (shiftedInnerPole d P.T (psi x)) t) K μ) := by
  obtain ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,hi⟩ :=
    exists_actual_inner_integral B rootB phi hphi hB hB0 hrB
  obtain ⟨ρ,hρ,hp⟩ := actual_shifted_pole_properties B phi hphi rP CP r hrP hr
  refine ⟨R₀,ρ,c,min σ (ρ^2),C,M,hρ,hc,lt_min hσ (sq_pos_of_pos hρ),hC,hM,?_⟩
  intro m d hd P K μ hμ hK psi hpsi he
  apply hi m K μ hμ hK psi hpsi (shiftedInnerPole d P.T)
  intro x hx
  have hq := he x hx
  have hn : ‖psi x‖<ρ := by
    have hsq := norm_sq_le_absoluteEnergy (psi x)
    have hh := hq.trans_le (min_le_right σ (ρ^2))
    nlinarith [norm_nonneg (psi x)]
  have hh := hp (2*m+1) d hd P (psi x) hn
  exact ⟨hq.trans_le (min_le_left _ _),hh.2.1,hh.2.2,hh.1⟩

end
end IsingBulk.Anisotropic.NegativeCycles
