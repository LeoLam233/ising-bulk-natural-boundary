import IsingBulk.Anisotropic.NegativeNormalForm.ActualNormalizedModel
import IsingBulk.Anisotropic.NegativeNormalForm.CentralErrorScale
import IsingBulk.Anisotropic.NegativeCycles.NormalizedCapIntegralAlgebra
import IsingBulk.Anisotropic.NegativeCycles.NormalizedCapUniform
import IsingBulk.Anisotropic.NegativeCycles.ActualNormalizedCapIntegrability

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- The literal transformed central residue cap, with its full constrained
Jacobian and the exact physical residue, approximates one half of M. Every
radius and error constant is selected before the growing particle order. -/
theorem exists_actual_central_cap_model_error (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (hrBn : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0:ℂ),rootB t^2=B t) :
    ∃delta R r Cp : ℝ, 0<delta ∧ 0<R ∧ 0<r ∧ 0<Cp ∧
      delta≤R/4 ∧ 4*R≤r ∧
      ∀ b : ContDiffBump (0:ℝ), b.rOut<delta^2 →
      ∃A : ℝ,0<A ∧ ∀ᶠ m : ℕ in atTop, Odd (m+1) →
      let d : ℂ := ((Real.pi/(m+1:ℕ):ℝ):ℂ)
      let H := centralHessian B phi d
      ∃ P : UniformProjectedWitness B phi hphi (m+1) d r Cp,
      ∃ J : UniformCorrectionWitness B phi hphi (m+1) d r Cp P R,
      ∀j : ℕ,8*(m+1)^2≤j →
      let Phi := fun y=>P.V (J.W y)
      let M := model (B (tau (m+1))) (rootB (tau (m+1))) H (Real.sin phi) (m+1) j
      let cap := ∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*
        constrainedResidueDensity B rootB phi hphi d P.T j (constrainedMap Phi (complexify m q))*
        constrainedJacobian Phi (complexify m q)
      ‖2*cap-M‖≤
        A*((m+1:ℕ)/Real.sqrt j+(m+1:ℕ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))*‖M‖ := by
  obtain ⟨delta₀,R,r,Cp,A,hd₀,hR,hr,hCp,hA,hdR,hRr,hmodel⟩ :=
    exists_actual_normalized_model_error B rootB phi hphi hB hBn hrB hrBn hsq
  have hRhalf : R≤r/2 := by linarith
  obtain ⟨a,ha,hidentity⟩ := normalized_cutoff_cap_uniform B rootB phi hphi hB hBn r Cp R hr hR hRhalf
  obtain ⟨s,hs,hintegrable⟩ := actual_normalized_cap_integrable B rootB phi hphi hB hrB hBn r Cp R hr hR hRhalf
  let delta := min delta₀ (min a s)
  have hd : 0<delta := lt_min hd₀ (lt_min ha hs)
  have hdold : delta≤delta₀ := min_le_left _ _
  have hda : delta≤a := (min_le_right _ _).trans (min_le_left _ _)
  have hds : delta≤s := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta,R,r,Cp,hd,hR,hr,hCp,hdold.trans hdR,hRr,?_⟩
  intro b hb
  have hbold : b.rOut<delta₀^2 := hb.trans_le ((sq_le_sq₀ hd.le hd₀.le).2 hdold)
  have hba : b.rOut≤a^2 := hb.le.trans ((sq_le_sq₀ hd.le ha.le).2 hda)
  have hbs : b.rOut≤s^2 := hb.le.trans ((sq_le_sq₀ hd.le hs.le).2 hds)
  obtain ⟨Ct,hCt,hmodels⟩ := hmodel b hbold
  obtain ⟨F,_hF,hphase⟩ := exists_central_period_uniform_loss B phi hB
  have hphases := (tendsto_add_atTop_nat 1).eventually hphase
  have hnear : ∀ᶠ N : ℕ in atTop, ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<delta := by
    have hh := winding_angle_complex_tendsto_zero (Metric.ball_mem_nhds (0:ℂ) hd)
    change ∀ᶠ N : ℕ in atTop, ((Real.pi/(N:ℝ):ℝ):ℂ)∈Metric.ball 0 delta at hh
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hnears := (tendsto_add_atTop_nat 1).eventually hnear
  refine ⟨A+Ct,add_pos hA hCt,?_⟩
  filter_upwards [hmodels,hphases,hnears] with m hmodels hphase hnear ho
  dsimp only
  obtain ⟨P,J,hcenter,herror⟩ := hmodels ho
  refine ⟨P,J,?_⟩
  intro j hj
  let d : ℝ := Real.pi/(m+1:ℕ)
  let c : ℂ := centralHessian B phi (d:ℂ)/((2*(m+1:ℕ):ℝ):ℂ)
  let Phi := fun y=>P.V (J.W y)
  have hdpos : 0<d := by dsimp [d]; positivity
  have hdnear : |d|<delta := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hnear
  have hFint : Integrable (fun q : Fin m→ℝ=>(shapeSpatialCutoff b q:ℂ)*
      constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
        (constrainedMap Phi (complexify m q))*constrainedJacobian Phi (complexify m q)) := by
    obtain ⟨k,hk⟩ := ho
    have hm : m=2*k := by omega
    subst m
    exact hintegrable k d (hdnear.trans_le hds) (ne_of_gt hdpos) P J j b hbs
  have hc : 0≤c.re := by
    dsimp [c]
    rw [Complex.div_ofReal_re]
    exact div_nonneg (by linarith [hphase.1]) (by positivity)
  have hkint := quadraticModel_cutoff_integrable_positive (n := m) j (tau (m+1))
    (tau_pos (m+1) (by omega)) c hc b
  have heq (q : Fin m→ℝ) := hidentity m d (hdnear.trans_le hda) P J hcenter j b hba q
  have heq' (q : Fin m→ℝ) :
      (shapeSpatialCutoff b q:ℂ)*constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
        (constrainedMap Phi (complexify m q))*constrainedJacobian Phi (complexify m q)=
      regularResidue B rootB phi hphi (d:ℂ) P.T 0*(shapeSpatialCutoff b q:ℂ)*
        normalizedFullDensity B rootB phi hphi (d:ℂ) P.T Phi (complexify m q)*
        quadraticModelKernel m j (tau (m+1)) c q := by
    simpa only [Phi,c,d,tau,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast] using heq q
  have hsplit := (normalized_integral_split _ _ _ _ _ hcenter heq' hFint hkint).2
  rw [hsplit]
  exact (herror j hj).trans (mul_le_mul_of_nonneg_right
    (central_errors_le_density_scale A Ct hCt.le (m+1) j) (norm_nonneg _))

end
end IsingBulk.Anisotropic.NegativeNormalForm
