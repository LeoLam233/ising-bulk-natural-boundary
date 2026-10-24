import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueActual
import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianEnvelope
import IsingBulk.Anisotropic.NegativeNormalForm.RelativeDensityAlgebra

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem norm_sq_le_absoluteEnergy {n : ℕ} (v : Config n) : ‖v‖^2≤absoluteEnergy v := by
  have hq := absoluteEnergy_nonneg v
  have hn : ‖v‖≤Real.sqrt (absoluteEnergy v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
  nlinarith [Real.sq_sqrt hq,norm_nonneg v]

theorem UniformCorrectionWitness.constrainedJacobian_energy_envelope {m : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi (m+1) d r C)
    (J : UniformCorrectionWitness B phi hphi (m+1) d r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) (u : Config m)
    (hu : ‖freeChartCLM m u‖≤R/4) :
    let E := Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
      (m+1:ℕ)*absoluteEnergy (freeChartCLM m u)
    let K := 8/(R/2)^2
    ‖constrainedJacobian (fun y => P.V (J.W y)) u‖≤Real.exp (K*E) ∧
      ‖constrainedJacobian (fun y => P.V (J.W y)) u-1‖≤K*E*Real.exp (K*E) := by
  obtain ⟨ell,hell,hbound⟩ := J.constrainedJacobian_log_bound B phi hphi d r C R P hr hR hRr u hu
  dsimp only
  let E := Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
    (m+1:ℕ)*absoluteEnergy (freeChartCLM m u)
  have hq0 := absoluteEnergy_nonneg (freeChartCLM m u)
  have hE : 0≤E := by dsimp [E]; positivity
  have hle : ‖ell‖≤(4/(R/2)^2)*E := by
    have hq := norm_sq_le_absoluteEnergy (freeChartCLM m u)
    have hs := Real.sqrt_nonneg ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))
    apply hbound.trans
    dsimp [E]
    rw [div_pow]
    have hnq : (m+1:ℕ)*‖freeChartCLM m u‖^2≤
        Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
          (m+1:ℕ)*absoluteEnergy (freeChartCLM m u) := by
      nlinarith [mul_le_mul_of_nonneg_left hq (show 0≤((m+1:ℕ):ℝ) by positivity)]
    have hh := mul_le_mul_of_nonneg_left hnq (show 0≤4/(R/2)^2 by positivity)
    convert hh using 1; ring
  have hle2 : (4/(R/2)^2)*E≤(8/(R/2)^2)*E := by gcongr; norm_num
  rw [←hell]
  constructor
  · exact (Complex.norm_exp_le_exp_norm ell).trans (Real.exp_le_exp.mpr (hle.trans hle2))
  · have he := complex_exp_error_envelope ell ((4/(R/2)^2)*E) hle
    have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle2)
      (show 0≤2*((4/(R/2)^2)*E) by positivity)
    apply he.trans
    convert hh using 1; ring

/-- Complete actual pulled-back residue density: original scalar residue,
all inverse Vandermonde factors, and the constrained Jacobian. Every radius
and constant is chosen before the dimension. -/
theorem exists_uniform_full_density_envelope (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hroot : AnalyticAt ℂ rootB 0) (hrootn : rootB 0≠0) (D : ℝ) (hD : 0≤D) :
    ∃ δ R r C K : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<C ∧ 0<K ∧ δ≤R/4 ∧ 4*R≤r ∧
      ∀ m : ℕ, ∀ d : ℂ, ‖d‖<δ → (m+1:ℕ)*‖d‖≤D →
      ∃ P : UniformProjectedWitness B phi hphi (m+1) d r C,
      ∃ J : UniformCorrectionWitness B phi hphi (m+1) d r C P R,
      ∀ u : Config m, ‖freeChartCLM m u‖<δ →
      let rho := normalizedFullDensity B rootB phi hphi d P.T (fun y => P.V (J.W y)) u
      let E := Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
        (m+1:ℕ)*absoluteEnergy (freeChartCLM m u)
      ‖rho‖≤Real.exp (K*E) ∧ ‖rho-1‖≤K*E*Real.exp (K*E) := by
  obtain ⟨δp,R,r,C,Kp,hδp,hR,hr,hC,hKp,hδpR,hRr,hex⟩ :=
    exists_uniform_vandermonde_density_error B phi hphi hB hBn D hD
  have hRhalf : R≤r/2 := by linarith
  obtain ⟨δr,Kr,hδr,hKr,hδrR,hraw⟩ := exists_actual_regularResidue_error
    B rootB phi hphi hB hBn hroot hrootn r C R D hr hC hR hRhalf hD
  let δ := min δp δr
  let Kj := 8/(R/2)^2
  have hKj : 0<Kj := by dsimp [Kj]; positivity
  refine ⟨δ,R,r,C,Kr+Kp+Kj,lt_min hδp hδr,hR,hr,hC,by positivity,
    (min_le_right _ _).trans hδrR,hRr,?_⟩
  intro m d hd hdD
  obtain ⟨P,J,hpair⟩ := hex (m+1) (by omega) d (hd.trans_le (min_le_left _ _)) hdD
  refine ⟨P,J,?_⟩
  intro u hu
  let y := freeChartCLM m u
  have hmy : ZeroMean y := freeChartCLM_zeroMean m u
  have hp := hpair y (hu.trans_le (min_le_left _ _)) hmy
  have hrho := hraw (m+1) (by omega) d (hd.trans_le (min_le_right _ _)) hdD P J y
    (hu.trans_le (min_le_right _ _)) hmy
  have hj := J.constrainedJacobian_energy_envelope B phi hphi d r C R P hr hR hRhalf u
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
end IsingBulk.Anisotropic.NegativeNormalForm
