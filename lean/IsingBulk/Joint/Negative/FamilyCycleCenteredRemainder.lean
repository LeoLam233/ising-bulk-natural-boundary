import IsingBulk.Joint.Negative.FamilyCycleWitnessRemainder
import IsingBulk.Anisotropic.NegativeCycles.CenteredWitnessRemainder

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_centered_witness_remainder (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta∈Q, B (0,eta)≠0)
    (hrB : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta)) (rP CP : ℝ) (hrP : 0<rP) :
    ∃(R₀ : ℂ→ℂ) (ρ c σ C M : ℝ),0<ρ ∧ 0<c ∧ 0<σ ∧ 0<C ∧ 1≤M ∧
      ∀ eta∈Q, ∀m : ℕ, ∀d : ℝ,|d|<ρ →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) rP CP,
      ∀s : ℝ,s<σ →
      let F := centeredInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m d s P.T
      AnalyticOnNhd ℂ F (ball 0 (c/(2*m+1:ℕ))) ∧
      (∀j : ℕ,‖iteratedDeriv j F 0/(j.factorial:ℂ)‖≤
        ((volume (centeredInnerSet (2*m) d s)).toReal*(C*remainderGaussianEnvelope M m))/
          ((c/(2*m+1:ℕ))/2)^j) ∧
      (∀j : ℕ,iteratedDeriv j F 0=∫q in centeredInnerSet (2*m) d s,
        iteratedDeriv j (actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m
          (centeredInnerAngles (2*m) d q) (P.T (shapeExtend (complexify (2*m) q)))) 0) ∧
      (∀q∈centeredInnerSet (2*m) d s,∀t∈ball 0 (c/(2*m+1:ℕ)),
        t≠P.T (shapeExtend (complexify (2*m) q)) →
        formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) t (shapeExtend (complexify (2*m) q))*
          cothHalf (fun u => poleEquation (familyMember B eta) phi hphi (d:ℂ) u (shapeExtend (complexify (2*m) q))) t=
        poleResidue (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T (shapeExtend (complexify (2*m) q))/
          (P.T (shapeExtend (complexify (2*m) q))-t)+
        actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m (centeredInnerAngles (2*m) d q)
          (P.T (shapeExtend (complexify (2*m) q))) t) ∧
      (∀t∈ball 0 (c/(2*m+1:ℕ)),IntegrableOn
        (fun q => actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m (centeredInnerAngles (2*m) d q)
          (P.T (shapeExtend (complexify (2*m) q))) t) (centeredInnerSet (2*m) d s)) := by
  obtain ⟨R₀,ρ,c,σ,C,M,hρ,hc,hσ,hC,hM,hw⟩ :=
    compact_family_actual_witness_remainder B rootB phi hphi hQ hB hB0 hrB rP CP hrP
  refine ⟨R₀,ρ,c,σ,C,M,hρ,hc,hσ,hC,hM,?_⟩
  intro eta heta m d hd P s hs
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  let S := centeredInnerSet (2*m) d s
  let K := centeredInnerCompact (2*m) d s
  have hK : IsCompact K := centeredInnerCompact_isCompact _ _ _
  have hSK : S⊆K := centeredInnerSet_subset_compact _ _ _
  have hrestrict : (volume.restrict S).restrict K=volume.restrict S := by
    rw [Measure.restrict_restrict hK.measurableSet,inter_eq_right.mpr hSK]
  have hmass : (volume.restrict S) K=volume S := by
    rw [Measure.restrict_apply hK.measurableSet,inter_eq_right.mpr hSK]
  have he : ∀q∈K,absoluteEnergy (centeredInnerAngles (2*m) d q)<σ := by
    intro q hq
    rw [centeredInnerAngles_energy]
    change constrainedSquaredRadius q≤s-(2*m+1:ℕ)*d^2 at hq
    linarith
  have hh := hw eta heta m (d:ℂ) (by simpa using hd) P K (volume.restrict S) inferInstance hK
    (centeredInnerAngles (2*m) d) (centeredInnerAngles_continuous _ _) he
  simp only [hrestrict,hmass,shiftedInnerPole_centered_angles] at hh
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_,?_⟩
  intro q hq t ht hne
  have hi := hh.2.2.2.1 q (hSK hq) t ht hne
  have hsub : (fun i => centeredInnerAngles (2*m) d q i-(d:ℂ))=
      shapeExtend (complexify (2*m) q) := by
    funext i
    simp only [centeredInnerAngles,Complex.ofReal_add,add_sub_cancel_left]
    exact (congrFun (shapeExtend_complexify (2*m) q) i).symm
  have hnshift := formFactorNumerator_shift (n := 2*m+1) B rootB phi hphi (d:ℂ)
  have hdshift := poleParameterDerivative_shift (n := 2*m+1) B phi hphi (d:ℂ)
  have heshift := poleEquation_shift (n := 2*m+1) B phi hphi (d:ℂ)
  dsimp only [B,rootB] at hnshift hdshift heshift
  simp_rw [hnshift,hdshift,heshift,hsub] at hi
  exact hi
  intro t ht
  have htI := hh.2.2.2.2 t ht
  change Integrable _ ((volume.restrict S).restrict K) at htI
  rw [hrestrict] at htI
  exact htI

end
end IsingBulk.Joint.Negative
