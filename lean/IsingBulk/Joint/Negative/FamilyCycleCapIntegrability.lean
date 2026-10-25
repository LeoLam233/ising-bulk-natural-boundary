import IsingBulk.Joint.Negative.FamilyCycleResidueAnalytic
import IsingBulk.Joint.Negative.FamilyCycleHomotopy
import IsingBulk.Anisotropic.NegativeCycles.ActualNormalizedCapIntegrability

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set MeasureTheory Metric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_normalized_cap_integrable (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ : ℝ,0<ρ ∧ ∀ eta∈Q, ∀m : ℕ, ∀d : ℝ, |d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀j : ℕ, ∀b : ContDiffBump (0:ℝ), b.rOut≤ρ^2 →
      let Phi := fun y=>P.V (J.W y)
      Integrable (fun q : Fin (2*m)→ℝ=>(shapeSpatialCutoff b q:ℂ)*
        constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j
          (constrainedMap Phi (complexify (2*m) q))*
        constrainedJacobian Phi (complexify (2*m) q)) := by
  obtain ⟨a,ha,har,hres⟩ := compact_family_actualResidue_analyticOnNhd B rootB phi hphi hQ hB hroot hBn r C hr
  obtain ⟨b,hb,_hbR,hsector⟩ := compact_family_actualHomotopy_pole_sector B phi hphi hQ hB hBn r C R hr hR hRr
  let ρ := min (a/8) (min (b/2) (min (R/4) (Real.pi/2)))
  have hρ : 0<ρ := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hρa : ρ≤a/8 := min_le_left _ _
  have hρb : ρ≤b/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρR : ρ≤R/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρpi : ρ≤Real.pi/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hρ,?_⟩
  intro eta heta m d hd hd0 P J j bump hbump
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  dsimp only
  apply cutoff_cap_integrable_of_local_analytic B rootB phi hphi (d:ℂ) P.T
    (fun y=>P.V (J.W y)) j ρ hρ.le bump hbump
  intro q hq
  dsimp only
  let y := freeChartCLM (2*m) (complexify (2*m) q)
  have hy : ‖y‖≤ρ := by
    dsimp [y]
    rw [freeChartCLM_eq_shapeExtend]
    exact norm_shapeExtend_complexify_le q hρ.le hq
  have hyR : ‖y‖<R/2 := by linarith
  have hmy : ZeroMean y := freeChartCLM_zeroMean _ _
  have hW := J.w_inverse y hyR.le
  have hV := P.v_inverse (J.W y) (hW.1.trans hRr)
  have hm : ZeroMean (P.V (J.W y)) := (hV.2.2.2 (hW.2.2.2 hmy)).1
  have hn : ‖P.V (J.W y)‖<a := by
    have hh := ((J.corrected_bounds B phi hphi (d:ℂ) r C R P hr hR hRr).2 y hyR.le).1
    linarith
  have hP := (J.corrected_bounds B phi hphi (d:ℂ) r C R P hr hR hRr).1 y (by simpa using hyR)
  have hN := hres eta heta m (d:ℂ) (by simpa only [Complex.norm_real,Real.norm_eq_abs] using (show |d|<a by linarith))
    P (P.V (J.W y)) (by simpa using hn)
  have hT := P.t_analytic (P.V (J.W y)) (by simpa using (show ‖P.V (J.W y)‖<2*r by linarith))
  refine ⟨hP,hm,hN,hT,?_⟩
  have htau : 0<1-Real.cos d := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by norm_num)
      (show |d|≤Real.pi by linarith) (abs_pos.mpr hd0)
    simpa only [Real.cos_abs,Real.cos_zero,sub_pos] using hh
  have hs := hsector eta heta (2*m+1) (by omega) d
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using (show |d|<b by linarith))
    P J (shapeExtend q)
    (by simpa only [y,freeChartCLM_eq_shapeExtend,shapeExtend_complexify] using (hy.trans (show ρ≤b by linarith)))
    (sum_shapeExtend q) 1 (by constructor <;> norm_num)
  have hnon : 0≤(∑i,shapeExtend q i^2)/(8*(2*m+1:ℕ)) := by positivity
  have hpos : 0<(P.T (P.V (J.W y))).re := by
    simpa only [correctedHomotopy,Complex.ofReal_one,one_smul,add_sub_cancel,
      y,freeChartCLM_eq_shapeExtend,shapeExtend_complexify] using lt_of_lt_of_le (by linarith) hs
  intro hz
  rw [hz,Complex.zero_re] at hpos
  linarith


end
end IsingBulk.Joint.Negative
