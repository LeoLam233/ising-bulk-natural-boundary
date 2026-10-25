import IsingBulk.Joint.Negative.FamilyDensityActual
import IsingBulk.Joint.Negative.FamilyVandermondeDensity

namespace IsingBulk.Joint.Negative
noncomputable section
open Set IsingBulk.Anisotropic.NegativeNormalForm
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Complete actual pulled-back residue density: original scalar residue,
all inverse Vandermonde factors, and the constrained Jacobian. Every radius
and constant is chosen before the dimension. -/
theorem compact_family_full_density_envelope (B rootB : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta ∈ Q, AnalyticAt ℂ B (0,eta)) (hBn : ∀ eta ∈ Q, B (0,eta)≠0)
    (hroot : ∀ eta ∈ Q, AnalyticAt ℂ rootB (0,eta)) (hrootn : ∀ eta ∈ Q, rootB (0,eta)≠0) (D : ℝ) (hD : 0≤D) :
    ∃ δ R r C K : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<C ∧ 0<K ∧ δ≤R/4 ∧ 4*R≤r ∧
      ∀ eta ∈ Q, ∀ m : ℕ, ∀ d : ℂ, ‖d‖<δ → (m+1:ℕ)*‖d‖≤D →
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi (m+1) d r C,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi (m+1) d r C P R,
      ∀ u : Config m, ‖freeChartCLM m u‖<δ →
      let rho := normalizedFullDensity (familyMember B eta) (familyMember rootB eta) phi hphi d P.T (fun y => P.V (J.W y)) u
      let E := Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
        (m+1:ℕ)*absoluteEnergy (freeChartCLM m u)
      ‖rho‖≤Real.exp (K*E) ∧ ‖rho-1‖≤K*E*Real.exp (K*E) := by
  obtain ⟨δp,R,r,C,Kp,hδp,hR,hr,hC,hKp,hδpR,hRr,hex⟩ :=
    compact_family_vandermonde_density_error B phi hphi hQ hB hBn D hD
  have hRhalf : R≤r/2 := by linarith
  obtain ⟨δr,Kr,hδr,hKr,hδrR,hraw⟩ := compact_family_actual_regularResidue_error
    B rootB phi hphi hQ hB hBn hroot hrootn r C R D hr hC hR hRhalf hD
  let δ := min δp δr
  let Kj := 8/(R/2)^2
  have hKj : 0<Kj := by dsimp [Kj]; positivity
  refine ⟨δ,R,r,C,Kr+Kp+Kj,lt_min hδp hδr,hR,hr,hC,by positivity,
    (min_le_right _ _).trans hδrR,hRr,?_⟩
  intro eta heta m d hd hdD
  obtain ⟨P,J,hpair⟩ := hex eta heta (m+1) (by omega) d (hd.trans_le (min_le_left _ _)) hdD
  refine ⟨P,J,?_⟩
  intro u hu
  let y := freeChartCLM m u
  have hmy : ZeroMean y := freeChartCLM_zeroMean m u
  have hp := hpair y (hu.trans_le (min_le_left _ _)) hmy
  have hrho := hraw eta heta (m+1) (by omega) d (hd.trans_le (min_le_right _ _)) hdD P J y
    (hu.trans_le (min_le_right _ _)) hmy
  have hj := J.constrainedJacobian_energy_envelope (familyMember B eta) phi hphi d r C R P hr hR hRhalf u
    (hu.le.trans ((min_le_right _ _).trans hδrR))
  dsimp only at hp hrho hj ⊢
  rw [normalizedFullDensity_factorization]
  have hq0 := absoluteEnergy_nonneg y
  have hE : 0≤Real.sqrt ((m+1:ℕ)*absoluteEnergy y)+(m+1:ℕ)*absoluteEnergy y := by positivity
  have hh := three_factor_exponential_error _ _ _ _ _ _
    (mul_nonneg hKr.le hE) (mul_nonneg hKp.le hE) (mul_nonneg hKj.le hE)
    hrho.1 hp.1 hj.1 hrho.2 hp.2 hj.2
  simpa only [←add_mul] using hh


end
end IsingBulk.Joint.Negative
