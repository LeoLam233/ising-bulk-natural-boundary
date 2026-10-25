import IsingBulk.Joint.Negative.FamilyCycleStokes
import IsingBulk.Anisotropic.NegativeCycles.ActualIntegralTransport

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_residue_integral_transport (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ : ℝ,0<ρ ∧ ∀ eta∈Q, ∀m : ℕ, ∀d : ℝ, |d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀j : ℕ, ∀bump : ContDiffBump (0:ℝ), bump.rOut≤ρ^2 →
      ∀a b : ParameterSpace (2*m), a≤b → a 0=0 → b 0=1 →
      (∀i : Fin (2*m),bump.rOut≤(b i.succ)^2) →
      (∀i : Fin (2*m),bump.rOut≤(a i.succ)^2) →
      let Phi := fun y => P.V (J.W y)
      let f := constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j
      let H := freeStraightHomotopy (constrainedMap Phi)
      (∫q in Icc (fun i => a i.succ) (fun i => b i.succ),
        (shapeSpatialCutoff bump q:ℂ)*f (constrainedMap Phi (complexify (2*m) q))*
          constrainedJacobian Phi (complexify (2*m) q))-
      (∫q in Icc (fun i => a i.succ) (fun i => b i.succ),
        (shapeSpatialCutoff bump q:ℂ)*f (complexify (2*m) q))=
      ∫x in Icc a b,cutoffError (shapeCylinderCutoff bump) (chainPullback (densityForm f) H) x := by
  obtain ⟨ρ₀,hρ₀,htransport⟩ := compact_family_residue_caps_transport B rootB phi hphi hQ hB hroot hBn r C R hr hR hRr
  let ρ := min ρ₀ (R/4)
  have hρ : 0<ρ := lt_min hρ₀ (by positivity)
  have hρ0 : ρ≤ρ₀ := min_le_left _ _
  have hρR : ρ≤R/4 := min_le_right _ _
  refine ⟨ρ,hρ,?_⟩
  intro eta heta m d hd hd0 P J j bump hbump a b hab ha hb hfront hback
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  dsimp only
  let Phi := fun y => P.V (J.W y)
  let f := constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
  have hPsi (q : Fin (2*m)→ℝ) (hq : constrainedSquaredRadius q≤bump.rOut) :
      DifferentiableAt ℂ (constrainedMap Phi) (complexify (2*m) q) := by
    have hnorm := norm_shapeExtend_complexify_le q hρ.le (hq.trans hbump)
    have hpoint : freeChartCLM (2*m) (complexify (2*m) q)∈ball 0 (R/2) := by
      simp only [mem_ball,dist_zero_right,freeChartCLM_eq_shapeExtend]
      linarith
    have hPhi := (J.corrected_bounds B phi hphi (d:ℂ) r C R P hr hR hRr).1 _ hpoint
    exact (((freeCoordinatesCLM (2*m)).analyticAt _).comp
      (hPhi.comp (f := freeChartCLM (2*m)) ((freeChartCLM (2*m)).analyticAt _))).differentiableAt
  have hρsq : ρ^2≤ρ₀^2 := by nlinarith
  have ht := htransport eta heta m d (hd.trans_le hρ0) hd0 P J j bump (hbump.trans hρsq) a b hab hfront hback
  dsimp only at ht
  rw [ha,hb,boxCapIntegral_one_eq bump _ _ a b hPsi,boxCapIntegral_zero_eq bump _ _ a b hPsi] at ht
  exact ht


end
end IsingBulk.Joint.Negative
