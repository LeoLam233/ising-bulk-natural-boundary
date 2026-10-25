import IsingBulk.Joint.Negative.FamilyCycleRealPole
import IsingBulk.Joint.Negative.FamilyCycleResidueAnalytic
import IsingBulk.Anisotropic.NegativeCycles.ActualCenteredPoleIntegral

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_centered_pole_integral (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ : ℝ,0<ρ ∧ ∀ eta∈Q, ∀m : ℕ, ∀d : ℝ,|d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C,
      ∀_J : UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀s : ℝ,s≤ρ^2 → ∃δ : ℝ,0<δ ∧
      (∀q∈centeredInnerSet (2*m) d s,δ≤‖P.T (shapeExtend (complexify (2*m) q))‖) ∧
      AnalyticOnNhd ℂ (centeredPoleIntegral (familyMember B eta) (familyMember rootB eta) phi hphi m d s P.T) (ball 0 δ) ∧
      (∀t : ℂ,‖t‖<δ → IntegrableOn (fun q =>
        poleResidue (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T (shapeExtend (complexify (2*m) q))/
          (P.T (shapeExtend (complexify (2*m) q))-t)) (centeredInnerSet (2*m) d s)) ∧
      (∀j : ℕ,IntegrableOn
        (fun q => constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexify (2*m) q))
          (centeredInnerSet (2*m) d s) ∧
        iteratedDeriv j (centeredPoleIntegral (familyMember B eta) (familyMember rootB eta) phi hphi m d s P.T) 0/(j.factorial:ℂ)=
          ∫q in centeredInnerSet (2*m) d s,
            constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexify (2*m) q)) := by
  obtain ⟨a,ha,_har,hraw⟩ := compact_family_actualResidue_analyticOnNhd B rootB phi hphi hQ hB hroot hBn r C hr
  obtain ⟨b,hb,hpos⟩ := compact_family_real_pole_positive B phi hphi hQ hB hBn r C R hr hR hRr
  let ρ := min (a/2) (min (b/2) (r/2))
  have hρ : 0<ρ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hρa : ρ≤a/2 := min_le_left _ _
  have hρb : ρ≤b/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρr : ρ≤r/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,hρ,?_⟩
  intro eta heta m d hd hd0 P J s hs
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  let S := centeredInnerSet (2*m) d s
  let K := centeredInnerCompact (2*m) d s
  have hK : IsCompact K := centeredInnerCompact_isCompact _ _ _
  have hSK : S⊆K := centeredInnerSet_subset_compact _ _ _
  have hrestrict : (volume.restrict S).restrict K=volume.restrict S := by
    rw [Measure.restrict_restrict hK.measurableSet,inter_eq_right.mpr hSK]
  have hy (q : Fin (2*m)→ℝ) (hq : q∈K) : ‖shapeExtend (complexify (2*m) q)‖≤ρ := by
    apply norm_shapeExtend_complexify_le q hρ.le
    change constrainedSquaredRadius q≤s-(2*m+1:ℕ)*d^2 at hq
    have hn : 0≤(2*m+1:ℕ)*d^2 := by positivity
    linarith
  have hlin : Continuous (fun q : Fin (2*m)→ℝ => shapeExtend (complexify (2*m) q)) := by
    simp_rw [shapeExtend_complexify]
    exact continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_shapeExtend_eval i))
  have ht (q : Fin (2*m)→ℝ) (hq : q∈K) :
      AnalyticAt ℂ P.T (shapeExtend (complexify (2*m) q)) :=
    P.t_analytic _ (by simpa using (show ‖shapeExtend (complexify (2*m) q)‖<2*r by have := hy q hq; linarith))
  have hT : ContinuousOn (fun q : Fin (2*m)→ℝ => P.T (shapeExtend (complexify (2*m) q))) K := by
    intro q hq
    exact ((ht q hq).continuousAt.comp (f := fun q : Fin (2*m)→ℝ => shapeExtend (complexify (2*m) q)) hlin.continuousAt).continuousWithinAt
  have hA : ContinuousOn (fun q : Fin (2*m)→ℝ =>
      poleResidue B rootB phi hphi (d:ℂ) P.T (shapeExtend (complexify (2*m) q))) K := by
    intro q hq
    have han := hraw eta heta m (d:ℂ) (by simpa using (show |d|<a by linarith)) P _
      (by simpa using (show ‖shapeExtend (complexify (2*m) q)‖<a by have := hy q hq; linarith))
    exact (han.continuousAt.comp (f := fun q : Fin (2*m)→ℝ => shapeExtend (complexify (2*m) q)) hlin.continuousAt).continuousWithinAt
  have hne (q : Fin (2*m)→ℝ) (hq : q∈K) : P.T (shapeExtend (complexify (2*m) q))≠0 := by
    have hp := hpos eta heta (2*m+1) (by omega) d (by linarith) hd0 P J (shapeExtend q)
      (by simpa only [←shapeExtend_complexify] using (hy q hq).trans (show ρ≤b by linarith))
      (sum_shapeExtend q)
    simp only [←shapeExtend_complexify] at hp
    intro he
    rw [he,Complex.zero_re] at hp
    linarith [hp.1,hp.2]
  obtain ⟨δ,hδ,hgap,han,hint,hjets⟩ := compact_pole_integral_analytic_taylor
    (μ := volume.restrict S) hK hA hT hne
  simp only [hrestrict] at han hjets
  refine ⟨δ,hδ,fun q hq => hgap q (hSK hq),han,?_,?_⟩
  · intro t ht
    have hi := hint t ht
    change Integrable _ ((volume.restrict S).restrict K) at hi
    rw [hrestrict] at hi
    exact hi
  · intro j
    have hj := hjets j
    have hi := hj.1
    change Integrable _ ((volume.restrict S).restrict K) at hi
    rw [hrestrict] at hi
    exact ⟨by simpa only [S,IntegrableOn,constrainedResidueDensity,freeChartCLM_eq_shapeExtend] using hi,
      by
        change iteratedDeriv j (fun t => ∫q in S,
          poleResidue B rootB phi hphi (d:ℂ) P.T (shapeExtend (complexify (2*m) q))/
          (P.T (shapeExtend (complexify (2*m) q))-t)) 0/(j.factorial:ℂ)=_
        simpa only [S,constrainedResidueDensity,freeChartCLM_eq_shapeExtend] using hj.2⟩

end
end IsingBulk.Joint.Negative
