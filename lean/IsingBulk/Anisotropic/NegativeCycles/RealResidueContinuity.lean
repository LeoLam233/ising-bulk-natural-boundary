import IsingBulk.Anisotropic.NegativeCycles.CutoffLocalization

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric
open scoped BigOperators

 theorem actual_real_residue_uniform_continuous (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ : ℝ,0<ρ ∧ ∀m j : ℕ, ∀d : ℝ, |d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀_J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      ContinuousOn (fun q => constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q))
        {q | constrainedSquaredRadius q≤ρ^2} := by
  obtain ⟨a,ha,har,hres⟩ := actualResidue_uniform_analyticOnNhd B rootB phi hphi hB hroot hBn r C hr
  obtain ⟨b,hb,_hbR,hsector⟩ := actualHomotopy_pole_uniform_sector B phi hphi hB hBn r C R hr hR hRr
  let ρ := min (a/2) (min (b/2) (min r (Real.pi/2)))
  have hρ : 0<ρ := lt_min (by positivity) (lt_min (by positivity) (lt_min hr (by positivity)))
  have hρa : ρ≤a/2 := min_le_left _ _
  have hρb : ρ≤b/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρr : ρ≤r := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρpi : ρ≤Real.pi/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hρ,?_⟩
  intro m j d hd hd0 P J q hq
  have hdC : ‖(d:ℂ)‖<ρ := by simpa using hd
  have htau : 0<1-Real.cos d := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by norm_num)
      (show |d|≤Real.pi by linarith) (abs_pos.mpr hd0)
    simpa only [Real.cos_abs,Real.cos_zero,sub_pos] using hh
  have hy := norm_shapeExtend_complexify_le q hρ.le hq
  have hT := P.t_analytic (shapeExtend (complexify (2*m) q)) (by simpa using (show ‖shapeExtend (complexify (2*m) q)‖<2*r by linarith))
  have hN := hres m (d:ℂ) (by linarith) P (shapeExtend (complexify (2*m) q)) (by simpa using (show ‖shapeExtend (complexify (2*m) q)‖<a by linarith))
  have hre := hsector (2*m+1) (by omega) d (by linarith) P J (shapeExtend q)
    (by simpa only [←shapeExtend_complexify] using hy.trans (show ρ≤b by linarith))
    (sum_shapeExtend q) 0 (by constructor <;> norm_num)
  simp only [correctedHomotopy,Complex.ofReal_zero,zero_smul,add_zero,←shapeExtend_complexify] at hre
  have htpos : 0<(P.T (shapeExtend (complexify (2*m) q))).re := by
    have hnon : 0≤(∑i,(shapeExtend q i)^2)/(8*(2*m+1:ℕ)) := by positivity
    linarith
  have hTn : P.T (shapeExtend (complexify (2*m) q))≠0 := by intro he; rw [he,Complex.zero_re] at htpos; linarith
  have hf := hN.div (hT.pow (j+1)) (pow_ne_zero _ hTn)
  have hfc : ContinuousAt (fun z : Config (2*m) =>
      poleResidue B rootB phi hphi (d:ℂ) P.T (freeChartCLM (2*m) z)/(P.T (freeChartCLM (2*m) z))^(j+1))
      (complexify (2*m) q) := by
    apply hf.continuousAt.comp_of_eq (freeChartCLM (2*m)).continuous.continuousAt
    exact freeChartCLM_eq_shapeExtend _ _
  exact (hfc.comp (show ContinuousAt (complexify (2*m)) q by unfold complexify; fun_prop)).continuousWithinAt

end IsingBulk.Anisotropic.NegativeCycles
