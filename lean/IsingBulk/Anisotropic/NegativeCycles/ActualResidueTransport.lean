import IsingBulk.Anisotropic.NegativeCycles.ActualResidueAnalytic
import IsingBulk.Anisotropic.NegativeCycles.FreeHomotopy

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric
open scoped BigOperators
set_option maxHeartbeats 800000

def constrainedResidueDensity {n : ℕ} (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (T : Config (n+1)→ℂ) (j : ℕ) (q : Config n) : ℂ :=
  poleResidue B rootB phi hphi d T (freeChartCLM n q)/(T (freeChartCLM n q))^(j+1)

/-- Stokes transport of the actual residue differential form along the actual corrected map.
All holomorphy and pole exclusion on the enlarged support are derived, not premises. -/
theorem actual_residue_caps_transport (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ : ℝ,0<ρ ∧ ∀m : ℕ, ∀d : ℝ, |d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀j : ℕ, ∀bump : ContDiffBump (0:ℝ), bump.rOut≤ρ^2 →
      ∀a b : ParameterSpace (2*m), a≤b →
      (∀i : Fin (2*m),bump.rOut≤(b i.succ)^2) →
      (∀i : Fin (2*m),bump.rOut≤(a i.succ)^2) →
      let f := constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
      let H := freeStraightHomotopy (constrainedMap (fun y => P.V (J.W y)))
      boxCapIntegral (fun x => shapeCylinderCutoff bump x • chainPullback (densityForm f) H x) a b (b 0)-
        boxCapIntegral (fun x => shapeCylinderCutoff bump x • chainPullback (densityForm f) H x) a b (a 0)=
        ∫x in Icc a b,cutoffError (shapeCylinderCutoff bump) (chainPullback (densityForm f) H) x := by
  obtain ⟨a,ha,har,hres⟩ := actualResidue_uniform_analyticOnNhd B rootB phi hphi hB hroot hBn r C hr
  obtain ⟨b,hb,_hbR,hsector⟩ := actualHomotopy_pole_uniform_sector B phi hphi hB hBn r C R hr hR hRr
  let ρ := min (a/4) (min (b/2) (min (R/4) (Real.pi/2)))
  have hρ : 0<ρ := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hρa : ρ≤a/4 := min_le_left _ _
  have hρb : ρ≤b/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρR : ρ≤R/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρpi : ρ≤Real.pi/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hρ,?_⟩
  intro m d hd hd0 P J j bump hbump lo hi hlo hfront hback
  dsimp only
  let Phi : Config (2*m+1)→Config (2*m+1) := fun y => P.V (J.W y)
  let H := freeStraightHomotopy (constrainedMap Phi)
  let f := constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
  have hdC : ‖(d:ℂ)‖<ρ := by simpa using hd
  have htau : 0<1-Real.cos d := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by norm_num)
      (show |d|≤Real.pi by linarith) (abs_pos.mpr hd0)
    simpa only [Real.cos_abs,Real.cos_zero,sub_pos] using hh
  have hpoint (x : ParameterSpace (2*m)) (hx : x 0∈Icc (-1/2:ℝ) (3/2))
      (hq : constrainedSquaredRadius (fun i => x i.succ)≤bump.rOut) :
      DifferentiableAt ℂ f (H x) ∧ ContDiffAt ℝ 2 H x := by
    let q : Fin (2*m)→ℝ := fun i => x i.succ
    let y : Config (2*m+1) := shapeExtend (complexify (2*m) q)
    have hyρ : ‖y‖≤ρ := norm_shapeExtend_complexify_le q hρ.le (hq.trans hbump)
    have hyR : ‖y‖≤R/2 := by linarith
    have hmy : ZeroMean y := sum_shapeExtend _
    have hmean := correctedHomotopy_zeroMean P J hRr (x 0) y hyR hmy
    have hEq : freeChartCLM (2*m) (H x)=correctedHomotopy P J (x 0) y := by
      rw [freeChartCLM_eq_shapeExtend]
      exact freeStraightHomotopy_constrained Phi x hmean.1
    have hnorm := correctedHomotopy_norm_le P J hr hR hRr (x 0) hx y hyR
    have hHa : ‖correctedHomotopy P J (x 0) y‖<a := by linarith
    have hHaR : ‖correctedHomotopy P J (x 0) y‖<2*r := by linarith
    have hT := P.t_analytic (correctedHomotopy P J (x 0) y) (by simpa using hHaR)
    have hN := hres m (d:ℂ) (by linarith) P (correctedHomotopy P J (x 0) y) (by simpa using hHa)
    have hre := hsector (2*m+1) (by omega) d (by linarith) P J (shapeExtend q)
      (by simpa only [←shapeExtend_complexify] using hyρ.trans (show ρ≤b by linarith))
      (sum_shapeExtend q) (x 0) hx
    have htpos : 0<(P.T (correctedHomotopy P J (x 0) y)).re := by
      have hnon : 0≤(∑i,(shapeExtend q i)^2)/(8*(2*m+1:ℕ)) := by positivity
      simpa only [←shapeExtend_complexify] using lt_of_lt_of_le (by linarith : 0<1-Real.cos d+(∑i,(shapeExtend q i)^2)/(8*(2*m+1:ℕ))) hre
    have hTn : P.T (correctedHomotopy P J (x 0) y)≠0 := by intro he; rw [he,Complex.zero_re] at htpos; linarith
    have hF : AnalyticAt ℂ (fun v => poleResidue B rootB phi hphi (d:ℂ) P.T v/(P.T v)^(j+1))
        (freeChartCLM (2*m) (H x)) := by
      rw [hEq]
      exact hN.div (hT.pow (j+1)) (pow_ne_zero _ hTn)
    refine ⟨(hF.comp (f := freeChartCLM (2*m)) ((freeChartCLM (2*m)).analyticAt (H x))).differentiableAt,?_⟩
    apply freeStraightHomotopy_contDiffAt
    have hPhi := (J.corrected_bounds B phi hphi (d:ℂ) r C R P hr hR hRr).1 y
      (show y∈ball 0 (R/2) by simpa using (show ‖y‖<R/2 by linarith))
    exact ((freeCoordinatesCLM (2*m)).analyticAt _).comp
      (hPhi.comp_of_eq ((freeChartCLM (2*m)).analyticAt (complexify (2*m) q)) (by simp [y,q]))
  exact constrained_cylinder_caps_transport bump f H (fun x hx hq => (hpoint x hx hq).1)
    (fun x hx hq => (hpoint x hx hq).2) hlo hfront hback

end IsingBulk.Anisotropic.NegativeCycles
