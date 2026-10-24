import IsingBulk.Anisotropic.NegativeCycles.NormalizedCapUniform
import IsingBulk.Anisotropic.NegativeCycles.NormalizedCapIntegralAlgebra

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric
open scoped BigOperators

/-- Actual uniform cap-to-model decomposition. Both cap and normalized error
integrability are proved internally, for every Taylor order. -/
theorem actual_normalized_cap_integral_uniform (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃η : ℝ,0<η ∧ ∀m : ℕ, ∀d : ℝ, |d|<η → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      regularResidue B rootB phi hphi (d:ℂ) P.T 0≠0 →
      ∀j : ℕ, ∀b : ContDiffBump (0:ℝ), b.rOut≤η^2 →
      let Phi := fun y=>P.V (J.W y)
      let center := regularResidue B rootB phi hphi (d:ℂ) P.T 0
      let D := fun q=>normalizedFullDensity B rootB phi hphi (d:ℂ) P.T Phi (complexify (2*m) q)
      let k := quadraticModelKernel (2*m) j (1-Real.cos d)
        (centralHessian B phi (d:ℂ)/(2*(2*m+1:ℕ)))
      let F := fun q=>(shapeSpatialCutoff b q:ℂ)*
        constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
          (constrainedMap Phi (complexify (2*m) q))*constrainedJacobian Phi (complexify (2*m) q)
      Integrable F ∧ Integrable (fun q=>(shapeSpatialCutoff b q:ℂ)*(D q-1)*k q) ∧
        (∀q,F q=center*(shapeSpatialCutoff b q:ℂ)*D q*k q) ∧
        (∫q,F q)=center*((∫q,(shapeSpatialCutoff b q:ℂ)*k q)+
          (∫q,(shapeSpatialCutoff b q:ℂ)*(D q-1)*k q)) := by
  obtain ⟨a,ha,hid⟩ := normalized_cutoff_cap_uniform B rootB phi hphi hB hBn r C R hr hR hRr
  obtain ⟨b,hb,hint⟩ := actual_normalized_cap_integrable B rootB phi hphi hB hroot hBn r C R hr hR hRr
  obtain ⟨c,hc,hpos⟩ := centralHessian_uniform_rightHalfPlane B phi hB
  let η := min a (min b (min c (Real.pi/2)))
  have hη : 0<η := lt_min ha (lt_min hb (lt_min hc (by positivity)))
  have hηa : η≤a := min_le_left _ _
  have hηb : η≤b := (min_le_right _ _).trans (min_le_left _ _)
  have hηc : η≤c := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηpi : η≤Real.pi/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨η,hη,?_⟩
  intro m d hd hd0 P J hcen j bump hbump
  dsimp only
  have hba : bump.rOut≤a^2 := hbump.trans (by nlinarith)
  have hbb : bump.rOut≤b^2 := hbump.trans (by nlinarith)
  have hF := hint m d (hd.trans_le hηb) hd0 P J j bump hbb
  have he := hid (2*m) d (hd.trans_le hηa) P J hcen j bump hba
  dsimp only at hF he
  have htau : 0<1-Real.cos d := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by norm_num)
      (show |d|≤Real.pi by linarith) (abs_pos.mpr hd0)
    simpa only [Real.cos_abs,Real.cos_zero,sub_pos] using hh
  have hH := hpos (d:ℂ) (by simpa using hd.trans_le hηc)
  have hcre : 0≤(centralHessian B phi (d:ℂ)/(2*(2*m+1:ℕ))).re := by
    have hh : (2*(2*m+1:ℕ):ℂ)=((2*(2*m+1:ℕ):ℝ):ℂ) := by push_cast; rfl
    rw [hh,Complex.div_ofReal_re]
    exact (div_pos hH (by positivity)).le
  have hk := quadraticModel_cutoff_integrable_positive (n := 2*m) j (1-Real.cos d) htau
    (centralHessian B phi (d:ℂ)/(2*(2*m+1:ℕ))) hcre bump
  have hi := normalized_integral_split _ _ _ _ _ hcen he hF hk
  exact ⟨hF,hi.1,he,hi.2⟩

end IsingBulk.Anisotropic.NegativeCycles
