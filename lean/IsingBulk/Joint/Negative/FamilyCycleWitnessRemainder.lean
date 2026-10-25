import IsingBulk.Joint.Negative.FamilyCycleInnerIntegral
import IsingBulk.Joint.Negative.FamilyCycleShiftedPole
import IsingBulk.Anisotropic.NegativeCycles.ActualWitnessRemainder

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_actual_witness_remainder (B rootB : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta∈Q, B (0,eta)≠0)
    (hrB : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta)) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ (R₀ : ℂ → ℂ) (ρ c σ C M : ℝ), 0<ρ ∧ 0<c ∧ 0<σ ∧ 0<C ∧ 1≤M ∧
      ∀ eta∈Q, ∀ m : ℕ, ∀ d : ℂ, ‖d‖<ρ →
      ∀ P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) d rP CP,
      ∀ (K : Set (Fin (2*m) → ℝ)) (μ : Measure (Fin (2*m) → ℝ)),
      IsFiniteMeasureOnCompacts μ → IsCompact K →
      ∀ psi : (Fin (2*m) → ℝ) → Config (2*m+1), Continuous psi →
      (∀ x∈K, absoluteEnergy (psi x)<σ) →
      let F := fun t => ∫ x in K,
        actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m (psi x) (shiftedInnerPole d P.T (psi x)) t ∂μ
      AnalyticOnNhd ℂ F (ball 0 (c/(2*m+1:ℕ))) ∧
      (∀ j : ℕ, ‖iteratedDeriv j F 0/(j.factorial:ℂ)‖≤
        ((μ K).toReal*(C*remainderGaussianEnvelope M m))/((c/(2*m+1:ℕ))/2)^j) ∧
      (∀ j : ℕ, iteratedDeriv j F 0=∫ x in K,
        iteratedDeriv j (actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m
          (psi x) (shiftedInnerPole d P.T (psi x))) 0 ∂μ) ∧
      (∀ x∈K, ∀ t∈ball 0 (c/(2*m+1:ℕ)), t≠shiftedInnerPole d P.T (psi x) →
        formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi 0 t (psi x)*
          cothHalf (fun u => poleEquation (familyMember B eta) phi hphi 0 u (psi x)) t=
        (-2*formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi 0 (shiftedInnerPole d P.T (psi x)) (psi x)/
          poleParameterDerivative (familyMember B eta) phi hphi 0 (shiftedInnerPole d P.T (psi x)) (psi x))/
          (shiftedInnerPole d P.T (psi x)-t)+
        actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m (psi x) (shiftedInnerPole d P.T (psi x)) t) ∧
      (∀ t∈ball 0 (c/(2*m+1:ℕ)), IntegrableOn
        (fun x => actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m (psi x)
          (shiftedInnerPole d P.T (psi x)) t) K μ) := by
  obtain ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,hi⟩ :=
    compact_family_actual_inner_integral B rootB phi hphi hQ hB hB0 hrB
  obtain ⟨ρ,hρ,hp⟩ := universal_shifted_pole_properties phi hphi rP CP r hrP hr
  refine ⟨R₀,ρ,c,min σ (ρ^2),C,M,hρ,hc,lt_min hσ (sq_pos_of_pos hρ),hC,hM,?_⟩
  intro eta heta m d hd P K μ hμ hK psi hpsi he
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  apply hi eta heta m K μ hμ hK psi hpsi (shiftedInnerPole d P.T)
  intro x hx
  have hq := he x hx
  have hn : ‖psi x‖<ρ := by
    have hsq := norm_sq_le_absoluteEnergy (psi x)
    have hh := hq.trans_le (min_le_right σ (ρ^2))
    nlinarith [norm_nonneg (psi x)]
  have hh := hp B (2*m+1) d hd P (psi x) hn
  exact ⟨hq.trans_le (min_le_left _ _),hh.2.1,hh.2.2,hh.1⟩

end
end IsingBulk.Joint.Negative
