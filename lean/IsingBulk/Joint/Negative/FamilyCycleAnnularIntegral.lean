import IsingBulk.Joint.Negative.FamilyCycleAnnularResidue
import IsingBulk.Anisotropic.NegativeCycles.ActualAnnularIntegralBound

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_annular_integral_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ M c : ℝ,0<ρ ∧ 1≤M ∧ 0<c ∧ ∀bump : ContDiffBump (0:ℝ), bump.rOut≤ρ^2 →
      ∃K : ℝ,0≤K ∧ ∀ eta∈Q, ∀m j : ℕ,0<m → ∀d : ℝ, |d|<ρ →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀a b : ParameterSpace (2*m), a 0=0 → b 0=1 →
      let f := constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j
      let H := freeStraightHomotopy (constrainedMap (fun y => P.V (J.W y)))
      ‖∫x in Icc a b,cutoffError (shapeCylinderCutoff bump) (chainPullback (densityForm f) H) x‖≤
        ((((2*m:ℕ):ℝ)+1)*K*
          ((2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
            ((8*(2*m+1:ℕ):ℝ)/bump.rIn)^(j+1))*
          Real.sqrt (((2*m:ℕ)*(2+ρ)^2)^(2*m)))*(volume (Icc a b)).toReal := by
  obtain ⟨δ,M,c,hδ,hM,hc,hres⟩ := compact_family_homotopy_residue_bound B rootB phi hphi hQ hB hroot hBn r C R hr hR hRr
  let ρ := min δ (R/4)
  have hρ : 0<ρ := lt_min hδ (by positivity)
  have hρδ : ρ≤δ := min_le_left _ _
  have hρR : ρ≤R/4 := min_le_right _ _
  refine ⟨ρ,M,c,hρ,hM,hc,?_⟩
  intro bump hbump
  obtain ⟨K,hK,hgradient⟩ := shapeCylinderCutoff_uniform_gradient bump
  refine ⟨K,hK,?_⟩
  intro eta heta m j hm d hd P J a b ha hb
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  dsimp only
  let Phi : Config (2*m+1)→Config (2*m+1) := fun y => P.V (J.W y)
  let f := constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
  let H := freeStraightHomotopy (constrainedMap Phi)
  have hbin := bump.rIn_pos
  apply constrained_cylinder_error_integral_bound (by omega) bump f H ha hb hK (by positivity) (by positivity)
  intro x hx hs hinner
  have htime : x 0∈Icc (0:ℝ) 1 := by
    constructor
    · simpa only [ha] using hx.1 0
    · simpa only [hb] using hx.2 0
  have htime' : x 0∈Icc (-1/2:ℝ) (3/2) := by constructor <;> linarith [htime.1,htime.2]
  have hq := (shapeCylinderCutoff_tsupport_subset bump hs).2
  let q : Fin (2*m)→ℝ := fun i => x i.succ
  let y : Config (2*m+1) := shapeExtend (complexify (2*m) q)
  have hyρ : ‖y‖≤ρ := norm_shapeExtend_complexify_le q hρ.le (hq.trans hbump)
  have hyR : ‖y‖≤R/2 := by linarith
  have hmean := correctedHomotopy_zeroMean P J hRr (x 0) y hyR (sum_shapeExtend _)
  have hEq : freeChartCLM (2*m) (H x)=correctedHomotopy P J (x 0) y := by
    rw [freeChartCLM_eq_shapeExtend]
    exact freeStraightHomotopy_constrained Phi x hmean.1
  refine ⟨hgradient (2*m) x htime hq,?_,?_⟩
  · have hh := hres eta heta m j d (hd.trans_le hρδ) P J (shapeExtend q)
      (by simpa only [←shapeExtend_complexify] using hyρ.trans hρδ)
      (sum_shapeExtend q) bump.rIn bump.rIn_pos hinner (x 0) htime'
    change ‖poleResidue B rootB phi hphi (d:ℂ) P.T (freeChartCLM (2*m) (H x))/
      (P.T (freeChartCLM (2*m) (H x)))^(j+1)‖≤_
    rw [hEq]
    simpa only [←shapeExtend_complexify] using hh
  · intro i k
    exact actualHomotopy_derivative_entries_bound B phi hphi (d:ℂ) r C R P J hr hR hRr hρ.le
      (by linarith) x htime' (hq.trans hbump) i k


end
end IsingBulk.Joint.Negative
