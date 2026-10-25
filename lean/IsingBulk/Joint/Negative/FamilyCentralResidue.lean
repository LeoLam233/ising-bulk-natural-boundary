import IsingBulk.Joint.Negative.FamilyPeriodLoss
import IsingBulk.Joint.Negative.FamilyDensityScalar
import IsingBulk.Anisotropic.NegativeNormalForm.CentralResidueSequence

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance
open scoped Topology

/-- Every actual central residue has the exact physical center and exact full
complex period normalization, uniformly along the winding sequence. -/
theorem compact_family_central_residue_sequence (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0)
    (hr : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hrn : ∀eta∈Q,rootB (0,eta)≠0)
    (hsq : ∃s : ℝ,0<s ∧ ∀eta∈Q,∀t : ℂ,‖t‖<s → rootB (t,eta)^2=B (t,eta)) :
    ∀ᶠ N : ℕ in atTop, ∀eta∈Q, Odd N →
      let d : ℂ := ((Real.pi/(N:ℝ):ℝ):ℂ)
      ∀ T : Config N → ℂ,T 0=1-Complex.cos d →
        regularResidue (familyMember B eta) (familyMember rootB eta) phi hphi d T 0=
          centralDensity (familyMember B eta (tau N)) (familyMember rootB eta (tau N)) (Real.sin phi) N ∧
        regularResidue (familyMember B eta) (familyMember rootB eta) phi hphi d T 0≠0 ∧
        ∀ j : ℕ,alpha N≤j →
          2*regularResidue (familyMember B eta) (familyMember rootB eta) phi hphi d T 0*
            shapePeriod (N-1) j (tau N) (centralHessian (familyMember B eta) phi d/(2*(N:ℂ)))=
            model (familyMember B eta (tau N)) (familyMember rootB eta (tau N)) (centralHessian (familyMember B eta) phi d) (Real.sin phi) N j := by
  obtain ⟨r,hrpos,hbranch⟩ := compact_family_parameter_nonzero B hQ hB hBn
  obtain ⟨s,hs,hroot⟩ := compact_family_parameter_nonzero rootB hQ hr hrn
  obtain ⟨u,hu,hsquare⟩ := hsq
  have hnear : ∀ᶠ N : ℕ in atTop, ‖(tau N:ℂ)‖<min r (min s u) := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      tau_complex_tendsto_zero.eventually (Metric.ball_mem_nhds (0:ℂ) (lt_min hrpos (lt_min hs hu)))
  obtain ⟨F,_hF,hphase⟩ := compact_family_central_period_loss B phi hQ hB
  filter_upwards [hnear,hphase,eventually_ge_atTop (3:ℕ)] with N hn hphase hN eta heta ho
  have hba := hbranch eta heta (tau N) (hn.trans_le (min_le_left _ _))
  have hrb := hroot eta heta (tau N) (hn.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hsq' := hsquare eta heta (tau N) (hn.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hp : AnalyticAt ℂ (familyMember B eta) (tau N) ∧
      familyMember B eta (tau N)≠0 ∧ familyMember rootB eta (tau N)≠0 ∧
      familyMember rootB eta (tau N)^2=familyMember B eta (tau N) :=
    ⟨hba.1.comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const),hba.2,hrb.2,hsq'⟩
  have hphase := hphase eta heta
  dsimp only
  intro T hT
  let d : ℂ := ((Real.pi/(N:ℝ):ℝ):ℂ)
  have hd : 1-Complex.cos d=(tau N:ℂ) := by
    simp only [d,tau,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_cos]
  have hcenter := regularResidue_center_normalized ho (familyMember B eta) (familyMember rootB eta) phi hphi d
    (hd.symm ▸ hp.1) T hT (hd.symm ▸ hp.2.1) (hd.symm ▸ hp.2.2.1) (hd.symm ▸ hp.2.2.2)
  rw [hd] at hcenter
  refine ⟨hcenter,?_,?_⟩
  · rw [hcenter]
    exact centralDensity_ne_zero _ _ _ (by omega) hp.2.1 hp.2.2.1 hphi
  · intro j hj
    exact regularResidue_complex_period_eq_model ho hN (familyMember B eta) (familyMember rootB eta) phi hphi d hd hp.1 T
      (hT.trans hd) hp.2.1 hp.2.2.1 hp.2.2.2 (by linarith [hphase.1]) j hj

end
end IsingBulk.Joint.Negative
